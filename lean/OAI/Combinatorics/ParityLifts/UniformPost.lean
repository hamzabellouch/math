import OAI.Combinatorics.ParityLifts.UniformRate

namespace OAI

namespace ParityWL.Complexity

lemma RBEval.pair {p q : FCode} {x y z : DataTree} {R S : ℝ}
    (h : RBEval p x R y) (hg : RBEval q x S z) : RBEval (.pair p q) x (R+S+1) (.node y z) := by
  obtain ⟨B,hB,h⟩ := h
  obtain ⟨C,hC,hg⟩ := hg
  exact ⟨B+C+1,hB.pair hC,by push_cast; linarith⟩

lemma RBEval.size_le {p : FCode} {x y : DataTree} {R : ℝ} (h : RBEval p x R y) :
    (y.size : ℝ) ≤ R := by
  obtain ⟨B,hB,h⟩ := h
  exact (by exact_mod_cast hB.bounds.2.1 : (y.size : ℝ) ≤ B).trans h

lemma RBEval.post {α β : Type} [TreeCodec α] [TreeCodec β] {f : α → β}
    {p : FCode} {x : DataTree} {a : α} {R : ℝ} (h : RBEval p x R (treeEncode a))
    (P : PolyProgram α β f) :
    RBEval (.seq p P.program.code) x (R+P.coefficient*(R+1)^P.degree+1) (treeEncode (f a)) := by
  have hp : (P.program.time a : ℝ) ≤ P.coefficient*(R+1)^P.degree := by
    have hb : (P.program.time a : ℝ) ≤ P.coefficient*((treeEncode a).size+1 : ℝ)^P.degree := by
      exact_mod_cast P.bound a
    apply hb.trans
    gcongr
    exact h.size_le
  exact (h.seq (P.program.run a).real).mono (by linarith)

noncomputable def PolyProgram.uniformPostStart :
    PolyProgram ((ℕ × ℕ) × BitFormula) (ℕ × (ℕ × BitFormula))
      (fun x => (x.1.2,(12*x.1.1,x.2))) := by
  let j := (PolyProgram.fst (ℕ × ℕ) BitFormula).comp (PolyProgram.fst ℕ ℕ)
  let k := (PolyProgram.fst (ℕ × ℕ) BitFormula).comp (PolyProgram.snd ℕ ℕ)
  let r := ((PolyProgram.const 12).pair j).comp PolyProgram.natMul
  exact k.pair (r.pair (PolyProgram.snd (ℕ × ℕ) BitFormula))

noncomputable def PolyProgram.pairLeaves : PolyProgram (ℕ × List BitFormula) (List (ℕ × BitFormula))
    (fun x => x.2.map (fun F => (x.1,F))) := by
  let P : PolyProgram (BitFormula × ℕ) (ℕ × BitFormula) (fun x => (x.2,x.1)) :=
    .expr (.pair TExpr.input.right TExpr.input.left) (by intro x; rfl)
  exact ((PolyProgram.snd ℕ (List BitFormula)).pair (PolyProgram.fst ℕ (List BitFormula))).comp P.mapWith

noncomputable def uniformPostCode (p : FCode) : FCode :=
  .seq PolyProgram.uniformPostStart.program.code
    (.seq (.seq (.pair .left (.seq .right (runtimeSparseCode BitLiteral)))
      PolyProgram.pairLeaves.program.code) p.any)

noncomputable def runtimeStepBudget (j N : ℕ) : ℕ :=
  (ParamPolyProgram.sparseStep BitLiteral).coefficient (12*j)*
    (literalSizeBound N+(treeEncode (12*j)).size+2)^
      ((ParamPolyProgram.sparseStep BitLiteral).degree (12*j))

lemma runtimeStepBudget_bound (j N : ℕ) (F : BitFormula)
    (hs : (treeEncode F).size ≤ literalSizeBound N) :
    (ParamPolyProgram.sparseStep BitLiteral).program.time (12*j,F) ≤ runtimeStepBudget j N := by
  apply (ParamPolyProgram.sparseStep BitLiteral).bound (12*j) F |>.trans
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  simp only [treeEncode_pair,DataTree.size]
  omega

lemma runtimeStepBudget_rate (j : ℕ) : ExpBound (fun N => (runtimeStepBudget j N : ℝ)) 0 := by
  let P := ParamPolyProgram.sparseStep BitLiteral
  have h := ((sparseSize_add_rate ((treeEncode (12*j)).size+2)).polypow (P.degree (12*j))).scale
    (P.coefficient (12*j)) (Nat.cast_nonneg _)
  simpa only [runtimeStepBudget,Nat.add_assoc,Nat.cast_mul,Nat.cast_pow] using h

lemma uniformPostCode_rate : ∃ D : ℕ, 0<D ∧ ∀ j : ℕ, 0<j → ∀ k : ℕ, ∀ p : FCode,
    ∀ W : ℕ → ℝ, ∀ r : ℝ, 0 ≤ r → ExpBound W r →
    (∀ N (F : BitFormula), (treeEncode F).size ≤ literalSizeBound N →
      F.length ≤ sparseDensity (12*j) N → (∀ C∈F,C.length ≤ 3) →
      ∃ b,RBEval p (treeEncode (k,F)) (W N) (treeEncode b) ∧ (b=true↔∃ a,bitSat a F)) →
    ∃ R : ℕ → ℝ, ExpBound R ((D : ℝ)/j+r) ∧
      ∀ {N : ℕ} (F : Formula N), ∃ b,
        RBEval (uniformPostCode p) (treeEncode ((j,k),minimizeList F.bitList)) (R N)
          (treeEncode b) ∧ (b=true↔F.Satisfiable) := by
  let d := PolyProgram.pairLeaves.degree
  refine ⟨2*(d+1)+2,by positivity,?_⟩
  intro j hj k p W r hr hW hp
  let S : ℕ → ℕ := fun N => literalSizeBound N+(treeEncode ((j,k) : ℕ × ℕ)).size+1
  have hS : ExpBound (fun N => (S N : ℝ)) 0 := by
    simpa only [S,Nat.add_assoc] using sparseSize_add_rate ((treeEncode ((j,k) : ℕ × ℕ)).size+1)
  let I := PolyProgram.uniformPostStart
  let A : ℕ → ℝ := fun N => I.coefficient*(S N+1 : ℝ)^I.degree
  have hA : ExpBound A 0 := by
    simpa only [A,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one] using polynomial_program_rate I S hS
  let Q := leafNumber j
  have hQ : ExpBound Q (1/(j : ℝ)) := ExpBound.exp _
  have hq : 0 ≤ 1/(j : ℝ) := by positivity
  let U : ℕ → ℝ := fun N => 4000*(2*Q N)^2*(literalSizeBound N+runtimeStepBudget j N+(treeEncode (12*j)).size+6 : ℕ)
  have hU : ExpBound U (2/(j : ℝ)) := by
    have hh := (((hQ.scale 2 (by norm_num)).pow 2).mul
      (((sparseSize_rate.add_same (runtimeStepBudget_rate j)).add_const (by norm_num)
        ((treeEncode (12*j)).size+6) (by positivity)))).scale 4000 (by norm_num)
    convert hh using 1
    · funext N; dsimp only [U,Q]; push_cast; ring
    · ring
  let V : ℕ → ℝ := fun N => 2*A N+U N+2
  have hV : ExpBound V (2/(j : ℝ)) := by
    have hh := ((hA.scale 2 (by norm_num)).add hU (by norm_num) (by positivity)).add_const (by positivity) 2 (by norm_num)
    simpa only [zero_add] using hh
  let K : ℕ → ℝ := fun N => V N+PolyProgram.pairLeaves.coefficient*(V N+1)^d+1
  have hK := hV.post (by positivity : 0 ≤ 2/(j : ℝ)) PolyProgram.pairLeaves.coefficient d
  let B : ℕ → ℝ := fun N => 500*(Q N+1)^2*(literalSizeBound N+(treeEncode k).size+1+W N+6)
  have hB : ExpBound B (2/(j : ℝ)+r) := by
    have hs := ((sparseSize_add_rate ((treeEncode k).size+1)).mono_rate hr).add_same hW |>.add_const hr 6 (by norm_num)
    have hh := (((hQ.add_const hq 1 (by norm_num)).pow 2).mul hs).scale 500 (by norm_num)
    convert hh using 1
    · funext N; dsimp only [B,Q]; push_cast; ring
    · ring
  let R : ℕ → ℝ := fun N => A N+(K N+B N+1)+1
  refine ⟨R,?_,?_⟩
  · have hh := (hA.add ((hK.add hB (by positivity) (by positivity)).add_const (by positivity) 1 (by norm_num))
       (by norm_num) (by positivity)).add_const (by positivity) 1 (by norm_num)
    convert hh using 1
    push_cast
    ring
  · intro N F
    obtain ⟨T,hroot,hvalid,hsize,hnum,hden,he⟩ := bit_sparse_certificate F j hj
    have hn : (T.leaves.length : ℝ) ≤ Q N := by simpa only [Q,leafNumber,one_div,inv_mul_eq_div] using hnum
    have hsz : (treeEncode ((j,k),T.root)).size ≤ S N := by
      simp only [treeEncode_pair,DataTree.size,S]
      have hh := hsize.root
      omega
    have ha : RBEval I.program.code (treeEncode ((j,k),T.root)) (A N) (treeEncode (k,(12*j,T.root))) := by
      apply (I.program.run ((j,k),T.root)).real.mono
      dsimp only [A]
      exact_mod_cast (I.bound ((j,k),T.root)).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hsz 1) _))
    have hu : RBEval (runtimeSparseCode BitLiteral) (treeEncode (12*j,T.root)) (U N) (treeEncode T.leaves.reverse) := by
      apply (runtimeSparseCode_run (12*j) (literalSizeBound N) (runtimeStepBudget j N)
        (runtimeStepBudget_bound j N) T hvalid hsize).real.mono
      rw [SparseTree.nodes_eq]
      dsimp only [U]
      push_cast
      gcongr
    have hz : ((treeEncode (k,(12*j,T.root))).size : ℝ) ≤ A N := ha.size_le
    have hl := (BEval.left (treeEncode (k,(12*j,T.root)))).real.mono hz
    have hh := (BEval.right (treeEncode (k,(12*j,T.root)))).real.mono hz
    have hv : RBEval (.pair .left (.seq .right (runtimeSparseCode BitLiteral)))
        (treeEncode (k,(12*j,T.root))) (V N) (treeEncode (k,T.leaves.reverse)) := by
      apply (hl.pair (hh.seq hu)).mono
      dsimp only [V]; linarith
    have hk := hv.post PolyProgram.pairLeaves
    obtain ⟨b,hb,hb'⟩ := RBEval.any p (fun x : ℕ × BitFormula => ∃ a,bitSat a x.2)
      (literalSizeBound N+(treeEncode k).size+1) (W N) (hW.1 N)
      (T.leaves.reverse.map (fun F => (k,F)))
      (by
        intro x hx
        obtain ⟨G,hG,rfl⟩ := List.mem_map.mp hx
        have hg := hsize.leaf G (List.mem_reverse.mp hG)
        simp only [treeEncode_pair,DataTree.size]; omega)
      (by
        intro x hx
        obtain ⟨G,hG,rfl⟩ := List.mem_map.mp hx
        have hg := List.mem_reverse.mp hG
        exact hp N G (hsize.leaf G hg) (hden G hg).1 (hden G hg).2)
    have hb'' : RBEval p.any (treeEncode (T.leaves.reverse.map (fun F => (k,F)))) (B N) (treeEncode b) := by
      apply hb.mono
      simp only [List.length_map,List.length_reverse]
      dsimp only [B]
      push_cast
      have hw := hW.1 N
      gcongr
    refine ⟨b,?_,?_⟩
    · rw [hroot] at ha hk
      exact ha.seq (hk.seq hb'')
    · exact hb'.trans ((by simp only [List.mem_map,List.mem_reverse]; aesop :
        (∃ x∈T.leaves.reverse.map (fun F => (k,F)),∃ a,bitSat a x.2)↔∃ G∈T.leaves,∃ a,bitSat a G).trans he)

end ParityWL.Complexity

end OAI
