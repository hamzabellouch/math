import OAI.Combinatorics.ParityLifts.LeafRate

namespace OAI

namespace ParityWL.Complexity

noncomputable def sparseStepBudget (j N : ℕ) : ℕ :=
  (PolyProgram.sparseStep BitLiteral (12*j)).coefficient*
    (literalSizeBound N+1)^(PolyProgram.sparseStep BitLiteral (12*j)).degree

lemma sparseStepBudget_rate (j : ℕ) : ExpBound (fun N => (sparseStepBudget j N : ℝ)) 0 :=
  polynomial_program_rate (PolyProgram.sparseStep BitLiteral (12*j)) literalSizeBound sparseSize_rate

lemma sparseStepBudget_bound (j N : ℕ) (F : BitFormula)
    (hs : (treeEncode F).size ≤ literalSizeBound N) :
    (PolyProgram.sparseStep BitLiteral (12*j)).program.time F ≤ sparseStepBudget j N := by
  apply (PolyProgram.sparseStep BitLiteral (12*j)).bound F |>.trans
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hs 1) _)

noncomputable def leafNumber (j N : ℕ) : ℝ := 2^((1/(j : ℝ))*N)

noncomputable def postBudget (j : ℕ) (W : ℕ → ℝ) (N : ℕ) : ℝ :=
  2010*(2*leafNumber j N)^2*(literalSizeBound N+sparseStepBudget j N+5 : ℕ)+
    500*(leafNumber j N+1)^2*(literalSizeBound N+W N+6)+1

noncomputable def postCode (j : ℕ) (p : FCode) : FCode := .seq (sparseCode BitLiteral (12*j)) p.any

lemma postCode_run (j : ℕ) (hj : 0<j) (p : FCode) (W : ℕ → ℝ)
    (hw : ∀ N, 0 ≤ W N)
    (hp : ∀ N (F : BitFormula), (treeEncode F).size ≤ literalSizeBound N →
      F.length ≤ sparseDensity (12*j) N → (∀ D∈F,D.length ≤ 3) →
      ∃ b,RBEval p (treeEncode F) (W N) (treeEncode b) ∧ (b=true↔∃ a,bitSat a F))
    {N : ℕ} (F : Formula N) :
    ∃ b, RBEval (postCode j p) (treeEncode (minimizeList F.bitList)) (postBudget j W N)
      (treeEncode b) ∧ (b=true↔F.Satisfiable) := by
  obtain ⟨T,hr,hv,hs,hnum,hden,he⟩ := bit_sparse_certificate F j hj
  have hn : (T.leaves.length : ℝ) ≤ leafNumber j N := by
    simpa only [leafNumber,one_div,inv_mul_eq_div] using hnum
  have ht := (sparseCode_run (12*j) (literalSizeBound N) (sparseStepBudget j N)
    (sparseStepBudget_bound j N) T hv hs).real
  have ht' : RBEval (sparseCode BitLiteral (12*j)) (treeEncode T.root)
      (2010*(2*leafNumber j N)^2*(literalSizeBound N+sparseStepBudget j N+5 : ℕ))
      (treeEncode T.leaves.reverse) := by
    apply ht.mono
    rw [SparseTree.nodes_eq]
    push_cast
    gcongr
  obtain ⟨b,hb,hb'⟩ := RBEval.any p (fun F : BitFormula => ∃ a,bitSat a F)
    (literalSizeBound N) (W N) (hw N) T.leaves.reverse
    (by intro G hG; exact hs.leaf G (List.mem_reverse.mp hG))
    (by
      intro G hG
      have hG' := List.mem_reverse.mp hG
      exact hp N G (hs.leaf G hG') (hden G hG').1 (hden G hG').2)
  have hb'' : RBEval p.any (treeEncode T.leaves.reverse)
      (500*(leafNumber j N+1)^2*(literalSizeBound N+W N+6)) (treeEncode b) := by
    apply hb.mono
    rw [List.length_reverse]
    have hwN := hw N
    gcongr
  rw [hr] at ht'
  exact ⟨b,ht'.seq hb'',hb'.trans ((by simp only [List.mem_reverse] :
    (∃ G∈T.leaves.reverse, ∃ a,bitSat a G)↔∃ G∈T.leaves,∃ a,bitSat a G).trans he)⟩

lemma postBudget_rate (j : ℕ) (W : ℕ → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hW : ExpBound W r) : ExpBound (postBudget j W) (2/(j : ℝ)+r) := by
  have hq : ExpBound (leafNumber j) (1/(j : ℝ)) := ExpBound.exp _
  have hq0 : 0 ≤ 1/(j : ℝ) := by positivity
  have hpoly : ExpBound (fun N => (literalSizeBound N+sparseStepBudget j N+5 : ℕ)) 0 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using
      (sparseSize_rate.add_same (sparseStepBudget_rate j)).add_same (ExpBound.const 5 (by norm_num))
  have ht := (((ExpBound.const 2 (by norm_num)).mul hq).pow 2).mul hpoly
  have ht' : ExpBound (fun N => 2010*(2*leafNumber j N)^2*(literalSizeBound N+sparseStepBudget j N+5 : ℕ)) (2/(j : ℝ)+r) := by
    have hh := (ExpBound.const 2010 (by norm_num)).mul ht
    simp only [zero_add,add_zero] at hh
    have hh' : ExpBound (fun N => 2010*((2*leafNumber j N)^2*(literalSizeBound N+sparseStepBudget j N+5 : ℕ))) (2/(j : ℝ)) := by
      convert hh using 1
      ring
    convert hh'.mono_rate (show 2/(j : ℝ) ≤ 2/(j : ℝ)+r by linarith) using 1
    funext N; ring
  have hsize := (sparseSize_rate.mono_rate hr).add_same hW |>.add_same
    ((ExpBound.const 6 (by norm_num)).mono_rate hr)
  have hl := (hq.add_same ((ExpBound.const 1 (by norm_num)).mono_rate hq0)).pow 2
  have ha := ((ExpBound.const 500 (by norm_num)).mul hl).mul hsize
  have ha' : ExpBound (fun N => 500*(leafNumber j N+1)^2*(literalSizeBound N+W N+6)) (2/(j : ℝ)+r) := by
    convert ha using 1
    ring
  exact (ht'.add_same ha').add_same ((ExpBound.const 1 (by norm_num)).mono_rate (by positivity))

end ParityWL.Complexity

end OAI
