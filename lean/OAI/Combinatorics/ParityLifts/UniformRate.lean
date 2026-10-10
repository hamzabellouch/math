import OAI.Combinatorics.ParityLifts.UniformMachine

namespace OAI

namespace ParityWL.Complexity

lemma TreeProgram.post_time_le {α β γ : Type} [TreeCodec α] [TreeCodec β] [TreeCodec γ]
    {f : α → β} {g : β → γ} (P : TreeProgram α β f) (Q : PolyProgram β γ g)
    (x : α) (T : ℝ) (hT : (P.time x : ℝ) ≤ T) :
    ((P.comp Q.program).time x : ℝ)  ≤  T+Q.coefficient*(T+1)^Q.degree+1 := by
  have hs : ((treeEncode (f x)).size : ℝ)  ≤  T :=
    (by exact_mod_cast (P.run x).bounds.2.1 : ((treeEncode (f x)).size : ℝ) ≤ P.time x).trans hT
  have hq : (Q.program.time (f x) : ℝ) ≤ Q.coefficient*((treeEncode (f x)).size+1 : ℝ)^Q.degree := by
    exact_mod_cast Q.bound (f x)
  have hq' : (Q.program.time (f x) : ℝ) ≤ Q.coefficient*(T+1)^Q.degree := by
    apply hq.trans
    gcongr
  change ((P.time x+Q.program.time (f x)+1 : ℕ) : ℝ) ≤ _
  push_cast
  linarith

lemma ExpBound.post {T : ℕ → ℝ} {r : ℝ} (hT : ExpBound T r) (hr : 0 ≤ r) (A d : ℕ) :
    ExpBound (fun N => T N+A*(T N+1)^d+1) ((d+1 : ℕ)*r) := by
  have hp := ((hT.add_const hr 1 (by norm_num)).pow d).scale A (Nat.cast_nonneg _)
  have h := (hT.add hp hr (by positivity)).add_const (by positivity) 1 (by norm_num)
  convert h using 1
  push_cast
  ring

lemma sparseSize_add_rate (a : ℕ) : ExpBound (fun N => (literalSizeBound N+a : ℕ)) 0 := by
  simpa only [Nat.cast_add] using sparseSize_rate.add_const (by norm_num) a (Nat.cast_nonneg _)

lemma uniformRawTime_rate : ∃ E : ℕ, 0<E ∧ ∀ t R : ℕ, 0<t →
    ∃ T : ℕ → ℝ, ExpBound T ((E : ℝ)*leafSlope t R) ∧
      ∀ N (F : BitFormula), (treeEncode F).size ≤ literalSizeBound N →
        F.length ≤ sparseDensity R N → (TreeProgram.uniformLeafOutput.time (t,F) : ℝ) ≤ T N := by
  obtain ⟨E,hE,hB⟩ := uniformLeafOutput_bound
  refine ⟨E,hE,?_⟩
  intro t R ht
  obtain ⟨C,d,hC,hB⟩ := hB t
  let S : ℕ → ℕ := fun N => literalSizeBound N+(treeEncode t).size+1
  have hS : ExpBound (fun N => (S N : ℝ)) 0 := by
    simpa only [S,Nat.add_assoc] using sparseSize_add_rate ((treeEncode t).size+1)
  let T : ℕ → ℝ := fun N => C*(S N+1 : ℝ)^d*2^((E : ℝ)*(leafSlope t R*N+6))
  refine ⟨T,?_,?_⟩
  · have hp := ((hS.add_const (by norm_num) 1 (by norm_num)).polypow d).scale C (Nat.cast_nonneg _)
    simpa only [zero_add] using hp.mul (ExpBound.affine_exp_mul E (leafSlope t R) 6)
  · intro N F hs hn
    have hb : (TreeProgram.uniformLeafOutput.time (t,F) : ℝ) ≤
        C*((treeEncode (t,F)).size+1 : ℝ)^d*2^((E : ℝ)*leafWords t F) := by
      rw [←nat_two_exp_cast]
      exact_mod_cast hB F
    have hsz : (treeEncode (t,F)).size ≤ S N := by
      simp only [treeEncode_pair,DataTree.size,S]
      omega
    have hq := sparse_leafWords_bound t R N ht F hn
    apply hb.trans
    dsimp only [T]
    gcongr
    · norm_num
    · exact hq

lemma uniformLeafTime_rate : ∃ E : ℕ, 0<E ∧ ∀ k : ℕ, 4 ≤ k → ∀ c : Convention, ∀ R : ℕ,
    ∃ T : ℕ → ℝ, ExpBound T ((E : ℝ)*leafSlope (bagParameter c k) R) ∧
      ∀ N (F : BitFormula), (treeEncode F).size ≤ literalSizeBound N →
        F.length ≤ sparseDensity R N → (uniformLeafTime c k F : ℝ) ≤ T N := by
  obtain ⟨E,hE,hRaw⟩ := uniformRawTime_rate
  let D := PolyProgram.withDimension.degree
  refine ⟨(D+1)*E,by positivity,?_⟩
  intro k hk c R
  let t := bagParameter c k
  have ht : 0<t := by cases c <;> simp only [t,bagParameter] <;> omega
  obtain ⟨U,hU,hUF⟩ := hRaw t R ht
  let I := (((PolyProgram.fst ℕ BitFormula).comp (PolyProgram.bagParameter c)).pair
    (PolyProgram.snd ℕ BitFormula))
  let S : ℕ → ℕ := fun N => literalSizeBound N+(treeEncode k).size+1
  have hS : ExpBound (fun N => (S N : ℝ)) 0 := by
    simpa only [S,Nat.add_assoc] using sparseSize_add_rate ((treeEncode k).size+1)
  let V : ℕ → ℝ := fun N => S N+I.coefficient*(S N+1 : ℝ)^I.degree+U N+2
  have hr : 0 ≤ (E : ℝ)*leafSlope t R := mul_nonneg (Nat.cast_nonneg _) (leafSlope_nonneg _ _)
  have hi := polynomial_program_rate I S hS
  have hV : ExpBound V ((E : ℝ)*leafSlope t R) := by
    have hm := ((hS.add_same hi).mono_rate hr).add_same hU |>.add_const hr 2 (by norm_num)
    simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one] using hm
  have hVF (N : ℕ) (F : BitFormula) (hs : (treeEncode F).size ≤ literalSizeBound N)
      (hn : F.length ≤ sparseDensity R N) : ((TreeProgram.uniformLeafPair c).time (k,F) : ℝ) ≤ V N := by
    have hsz : (treeEncode (k,F)).size ≤ S N := by simp only [treeEncode_pair,DataTree.size,S]; omega
    have hsz' : ((treeEncode (k,F)).size : ℝ) ≤ S N := by exact_mod_cast hsz
    have hb := (I.bound (k,F)).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hsz 1) _))
    have hb' : (I.program.time (k,F) : ℝ) ≤ I.coefficient*(S N+1 : ℝ)^I.degree := by exact_mod_cast hb
    have hu := hUF N F hs hn
    change (( (treeEncode (k,F)).size+(I.program.time (k,F)+TreeProgram.uniformLeafOutput.time (t,F)+1)+1 : ℕ) : ℝ) ≤ _
    dsimp only [V]
    push_cast
    linarith
  refine ⟨fun N => V N+PolyProgram.withDimension.coefficient*(V N+1)^D+1,?_,?_⟩
  · convert hV.post hr PolyProgram.withDimension.coefficient D using 1
    push_cast
    ring
  · intro N F hs hn
    exact TreeProgram.post_time_le (TreeProgram.uniformLeafPair c) PolyProgram.withDimension (k,F) (V N) (hVF N F hs hn)

lemma uniformLeafCost_rate : ∃ P : ℕ, 0<P ∧ ∀ k : ℕ, 4 ≤ k → ∀ c : Convention, ∀ R : ℕ,
    ∀ M : Machine, ∀ C r : ℝ, 0<C → 0 ≤ r →
    ∃ W : ℕ → ℝ, ExpBound W ((P : ℝ)*(r+1)*leafSlope (bagParameter c k) R) ∧
      ∀ N (F : BitFormula), (treeEncode F).size ≤ literalSizeBound N →
        F.length ≤ sparseDensity R N → uniformLeafCost c k M C r F ≤ W N := by
  obtain ⟨E,hE,hT⟩ := uniformLeafTime_rate
  let P := (simulationDegree+1)*(E+1)
  refine ⟨P,by dsimp [P]; positivity,?_⟩
  intro k hk c R M C r hC hr
  obtain ⟨T,hT,hTF⟩ := hT k hk c R
  let t := bagParameter c k
  have ht : 0<t := by cases c <;> simp only [t,bagParameter] <;> omega
  let s := leafSlope t R
  have hs : 0 ≤ s := leafSlope_nonneg _ _
  let U : ℕ → ℝ := fun N => C*2^(r*(s*N+6))
  have hU : ExpBound U (r*s) := (ExpBound.affine_exp_mul r s 6).scale C hC.le
  let W : ℕ → ℝ := fun N => T N+simulationCoefficient M*(T N+U N+1)^simulationDegree+negateCost+2
  have ha : 0 ≤ (E : ℝ)*s := by positivity
  have hb : 0 ≤ r*s := by positivity
  have hinner := (hT.add hU ha hb).add_const (by positivity) 1 (by norm_num)
  have hpow := (hinner.pow simulationDegree).scale (simulationCoefficient M) (Nat.cast_nonneg _)
  have hW := ((hT.add hpow ha (by positivity)).add_const (by positivity) negateCost (Nat.cast_nonneg _)).add_const (by positivity) 2 (by norm_num)
  refine ⟨W,hW.mono_rate ?_,?_⟩
  · change (E : ℝ)*s+(simulationDegree : ℝ)*((E : ℝ)*s+r*s) ≤ (P : ℝ)*(r+1)*s
    dsimp only [P]
    push_cast
    have h₁ := mul_nonneg (mul_nonneg (Nat.cast_nonneg (α:=ℝ) E) hr) hs
    have h₂ := mul_nonneg (Nat.cast_nonneg (α:=ℝ) simulationDegree) h₁
    have h₃ := mul_nonneg hr hs
    nlinarith
  · intro N F hsz hlen
    have ht' := hTF N F hsz hlen
    have hq := sparse_leafWords_bound t R N ht F hlen
    have hu : C*2^(r*leafWords t F) ≤ U N := by
      dsimp only [U]
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      exact mul_le_mul_of_nonneg_left hq hr
    exact cost_mono (uniformLeafTime c k F) (T N) (C*2^(r*leafWords t F)) (U N)
      (simulationCoefficient M) negateCost simulationDegree (Nat.cast_nonneg _)
      (mul_nonneg hC.le (Real.rpow_nonneg (by norm_num) _)) (Nat.cast_nonneg _) ht' hu

end ParityWL.Complexity

end OAI
