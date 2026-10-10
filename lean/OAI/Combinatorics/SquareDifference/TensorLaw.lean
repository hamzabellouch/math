import OAI.Combinatorics.SquareDifference.OutsideFourier

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open Finset

section TensorExpansion

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀j,Fintype (X j)] [∀j,DecidableEq (X j)]
  (L E : ∀j,((V → X j) → ℝ) →ₗ[ℝ] ℝ)

noncomputable def mixedTensorLaw (B : Finset J) : ((V → ∀j,X j) → ℝ) →ₗ[ℝ] ℝ :=
  tensorLaw (fun j => if j∈B then E j else L j)

lemma mixedTensorLaw_empty : mixedTensorLaw L E ∅=tensorLaw L := by
  simp only [mixedTensorLaw,Finset.notMem_empty,ite_false]

lemma mixedTensorLaw_nonneg (hL : ∀j F,(∀z,0≤F z) → 0≤L j F)
    (hE : ∀j F,(∀z,0≤F z) → 0≤E j F) (B : Finset J) (F : (V → ∀j,X j) → ℝ)
    (hF : ∀z,0≤F z) : 0 ≤ mixedTensorLaw L E B F := by
  apply tensorLaw_nonneg _ _ F hF
  intro j G hG
  split_ifs
  · exact hE j G hG
  · exact hL j G hG

lemma mixedTensorLaw_mass (hL : ∀j,L j (fun _ => 1)=1) (B : Finset J) :
    mixedTensorLaw L E B (fun _ => 1)=∏j∈B,E j (fun _ => 1) := by
  have hh := tensorLaw_fubini (fun j => if j∈B then E j else L j) (fun _ _ => 1)
  have he (j : J) : (if j∈B then E j else L j) (fun _ => 1)=if j∈B then E j (fun _ => 1) else 1 := by
    by_cases hj : j∈B <;> simp only [hj,ite_true,ite_false,hL]
  simpa only [prod_const_one,he,prod_ite_mem,univ_inter,mixedTensorLaw] using hh

lemma tensorLaw_scalar (c : J → ℝ) (F : (V → ∀j,X j) → ℝ) :
    tensorLaw (fun j => c j • L j) F=(∏j,c j)*tensorLaw L F := by
  change (∑z : ∀j,V → X j,(∏j,lawDensity (c j • L j) (z j))*F (fun v j => z j v))=_
  simp only [lawDensity,LinearMap.smul_apply,smul_eq_mul,prod_mul_distrib,mul_assoc,←mul_sum]
  rfl

lemma tensorLaw_sub_expansion (F : (V → ∀j,X j) → ℝ) :
    tensorLaw (fun j => L j-E j) F=
      ∑B : Finset J,(-1:ℝ)^B.card*mixedTensorLaw L E B F := by
  change (∑z : ∀j,V → X j,(∏j,lawDensity (L j-E j) (z j))*F (fun v j => z j v))=_
  simp only [lawDensity,LinearMap.sub_apply]
  simp_rw [prod_sub]
  simp only [powerset_univ,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro B _
  change (∑x : ∀j,V → X j,_) = (-1:ℝ)^B.card*(∑x : ∀j,V → X j,_)
  rw [mul_sum]
  apply sum_congr rfl
  intro z _
  have he : (∏j,lawDensity (if j∈B then E j else L j) (z j))=
      (∏j∈univ\B,lawDensity (L j) (z j))*(∏j∈B,lawDensity (E j) (z j)) := by
    rw [←prod_mul_prod_compl B (fun j => lawDensity (if j∈B then E j else L j) (z j))]
    have h₁ : (∏j∈B,lawDensity (if j∈B then E j else L j) (z j))=∏j∈B,lawDensity (E j) (z j) := by
      apply prod_congr rfl
      intro j hj
      rw [ite_eq_left hj]
    have h₂ : (∏j∈Bᶜ,lawDensity (if j∈B then E j else L j) (z j))=∏j∈Bᶜ,lawDensity (L j) (z j) := by
      apply prod_congr rfl
      intro j hj
      rw [ite_eq_right (mem_compl.mp hj)]
    rw [h₁,h₂,mul_comm]
    rfl
  change (-1:ℝ)^B.card*(_)*(_)*_=(-1:ℝ)^B.card*((∏j,lawDensity (if j∈B then E j else L j) (z j))*_)
  rw [he]
  simp only [lawDensity]
  ring

lemma tensorLaw_exceptional_bound (_ : ∀j,L j (fun _ => 1)=1)
    (G : ∀j,((V → X j) → ℝ) →ₗ[ℝ] ℝ) (eta : J → ℝ)
    (heta : ∀j,eta j∈Set.Icc (0:ℝ) 1)
    (hdec : ∀j,L j-E j=(1-eta j) • G j)
    (F : (V → ∀j,X j) → ℝ) :
    |tensorLaw L F|≤|tensorLaw G F|+
      ∑B∈(univ : Finset (Finset J)).erase ∅,|mixedTensorLaw L E B F| := by
  have he := tensorLaw_sub_expansion L E F
  simp_rw [hdec] at he
  rw [tensorLaw_scalar] at he
  rw [←sum_erase_add _ _ (mem_univ (∅ : Finset J))] at he
  simp only [card_empty,pow_zero,one_mul,mixedTensorLaw_empty] at he
  have hc : 0≤∏j,(1-eta j) := prod_nonneg (fun j _ => sub_nonneg.mpr (heta j).2)
  have hc' : (∏j,(1-eta j))≤1 := prod_le_one₀ (fun j _ => sub_nonneg.mpr (heta j).2)
    (fun j _ => sub_le_self _ (heta j).1)
  have ha : |(∏j,(1-eta j))*tensorLaw G F|≤|tensorLaw G F| := by
    rw [abs_mul,abs_of_nonneg hc]
    exact mul_le_of_le_one_left (abs_nonneg _) hc'
  have hb : |∑B∈(univ : Finset (Finset J)).erase ∅,(-1:ℝ)^B.card*mixedTensorLaw L E B F|≤
      ∑B∈(univ : Finset (Finset J)).erase ∅,|mixedTensorLaw L E B F| := by
    apply (abs_sum_le_sum_abs _ _).trans
    exact sum_le_sum (fun B _ => by simp only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,le_refl])
  have he' : tensorLaw L F=(∏j,(1-eta j))*tensorLaw G F-
      ∑B∈(univ : Finset (Finset J)).erase ∅,(-1:ℝ)^B.card*mixedTensorLaw L E B F := by linarith
  rw [he']
  exact (abs_sub _ _).trans (add_le_add ha hb)

end TensorExpansion

end SquareDifference

namespace SquareDifference

open Finset

section TensorFreeze

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀j,Fintype (X j)] [∀j,DecidableEq (X j)]
  (M L : ∀j,((V → X j) → ℝ) →ₗ[ℝ] ℝ)

noncomputable def frozenTensorLaw (B : Finset J) : ((V → ∀j,X j) → ℝ) →ₗ[ℝ] ℝ where
  toFun F := tensorLaw M (fun z => tensorLaw L (fun x => F (fun v j => if j∈B then z v j else x v j)))
  map_add' F G := by
    simp only [Pi.add_apply]
    simp only [←Pi.add_def,map_add]
  map_smul' c F := by
    simp only [Pi.smul_apply,←Pi.smul_def,map_smul,RingHom.id_apply]

lemma tensorLaw_freeze (B : Finset J) (hL : ∀j,L j (fun _ => 1)=1)
    (hML : ∀j,j∉B → M j=L j) (F : (V → ∀j,X j) → ℝ) :
    tensorLaw M (fun z => tensorLaw L (fun x => F (fun v j => if j∈B then z v j else x v j)))=tensorLaw M F := by
  have hd (y : V → ∀j,X j) : lawDensity (frozenTensorLaw M L B) y=lawDensity (tensorLaw M) y := by
    change tensorLaw M (fun z => tensorLaw L (fun x => if (fun v j => if j∈B then z v j else x v j)=y then 1 else 0))=_
    have hind (z x : V → ∀j,X j) :
        (if (fun v j => if j∈B then z v j else x v j)=y then (1:ℝ) else 0)=
        ∏j,if j∈B then (if (fun v => z v j)=(fun v => y v j) then 1 else 0)
          else (if (fun v => x v j)=(fun v => y v j) then 1 else 0) := by
      have he : (fun v j => if j∈B then z v j else x v j)=y ↔
          ∀j,(if j∈B then (fun v => z v j) else (fun v => x v j))=(fun v => y v j) := by
        constructor
        · intro h j; funext v; simpa only [ite_apply] using congrFun (congrFun h v) j
        · intro h; funext v j; simpa only [ite_apply] using congrFun (h j) v
      simp only [he]
      rw [←prod_indicator_forall]
      apply prod_congr rfl
      intro j _
      split_ifs <;> rfl
    simp_rw [hind]
    have hi (z : V → ∀j,X j) :
        tensorLaw L (fun x => ∏j,if j∈B then (if (fun v => z v j)=(fun v => y v j) then 1 else 0)
          else (if (fun v => x v j)=(fun v => y v j) then 1 else 0))=
        ∏j,if j∈B then (if (fun v => z v j)=(fun v => y v j) then 1 else 0)
          else lawDensity (L j) (fun v => y v j) := by
      rw [tensorLaw_fubini L (fun j w => if j∈B then (if (fun v => z v j)=(fun v => y v j) then 1 else 0)
        else (if w=(fun v => y v j) then 1 else 0))]
      apply prod_congr rfl
      intro j _
      by_cases hj : j∈B
      · simp only [hj,ite_true]
        by_cases hz : (fun v => z v j)=(fun v => y v j)
        · simp only [hz,ite_true,hL]
        · simp only [hz,ite_false]
          exact (L j).map_zero
      · simp only [hj,ite_false,lawDensity]
    simp_rw [hi]
    rw [tensorLaw_fubini M (fun j w => if j∈B then (if w=(fun v => y v j) then 1 else 0)
      else lawDensity (L j) (fun v => y v j)),tensorLaw_density]
    apply prod_congr rfl
    intro j _
    by_cases hj : j∈B
    · simp only [hj,ite_true,lawDensity]
    · simp only [hj,ite_false,hML j hj]
      simpa only [Pi.smul_def,smul_eq_mul,mul_one,hL] using
        (L j).map_smul (lawDensity (L j) (fun v => y v j)) (fun _ => (1:ℝ))
  change frozenTensorLaw M L B F=tensorLaw M F
  rw [linearFunctional_density (frozenTensorLaw M L B),linearFunctional_density (tensorLaw M)]
  exact sum_congr rfl (fun y _ => congrArg (fun t => t*F y) (hd y))

end TensorFreeze

end SquareDifference

end

end OAI
