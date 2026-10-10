import Mathlib
import OAI.Probability.LogConcave.Complexity.ProductEnergyBudgetScaled
import OAI.Probability.LogConcave.JetEstimates.Slice

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical NNReal BigOperators
open TensorEnergy

lemma tensorLie_scaled_energy {S : Type} [Fintype S] {d : ℕ}
    {H : Point d → ℝ} (hH : PolySmooth H) (ht : HasGaussianLowerTail H)
    {K : ℝ≥0} (hL : LipschitzWith K (gradient H))
    (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (F : (S → Fin d) → Point d → ℝ)
    (hA : ∀c,PolySmooth (A c)) (hF : ∀c,PolySmooth (F c))
    (C D B : ℕ → ℝ) {α κ ρ : ℝ} (hκ : 0 ≤ κ) (hρ : 1 ≤ ρ) (hB : ∀k,0 ≤ B k)
    (hb : ∀k y, AllSplitBound (spatialTensor A (List.finRange k) y) (C k*α*ρ^k))
    (hs : ∀k,0<k → ∀y,AllSplitBound (spatialTensor (scoreField H) (List.finRange k) y) (D k*ρ^k))
    (he : ∀k,0<k → spatialEnergy F k (gibbs H) ≤ κ*ρ^(2*k)*B k) (j : ℕ) :
    spatialEnergy (tensorLie H A F) j (gibbs H) ≤
      κ*α^2*ρ^(2*(j+2))*adjointEnergyBudget K D (productEnergyBudget C B) j := by
  have hi (k : ℕ) : productEnergyBudget (fun k => C k*α*ρ^k)
      (fun k => spatialEnergy F k (gibbs H)) k ≤
      κ*α^2*ρ^(2*(k+1))*productEnergyBudget C B k := by
    apply (productEnergyBudget_mono _ k (fun i hi _ => he i hi)).trans_eq
    exact productEnergyBudget_scaled C B α κ ρ k
  have hstep := tensorLie_energy (j:=j) hH ht hL A F hA hF
    (fun k => C k*α*ρ^k) (fun k => D k*ρ^k) (fun k _ => hb k) (fun k hk _ => hs k hk)
  have hm := adjointEnergyBudget_mono K.2 (fun k => D k*ρ^k) j (fun k _ => hi k)
  have hscale := adjointEnergyBudget_scaled K.2 (mul_nonneg hκ (sq_nonneg α)) hρ
    D (productEnergyBudget C B) (productEnergyBudget_nonneg hB) 1 j
  apply (hstep.trans (hm.trans hscale)).trans_eq
  rw [show j+1+1=j+2 by omega]
  congr 1

def iterTensorLie {S : Type} {d : ℕ} (H : Point d → ℝ)
    (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (F : (S → Fin d) → Point d → ℝ) :
    ℕ → (S → Fin d) → Point d → ℝ
  | 0 => F
  | n+1 => tensorLie H A (iterTensorLie H A F n)

def iterEnergyBudget (K : ℝ) (C D B : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => B
  | n+1 => adjointEnergyBudget K D (productEnergyBudget C (iterEnergyBudget K C D B n))

lemma iterEnergyBudget_nonneg {K : ℝ} (hK : 0 ≤ K) (C D : ℕ → ℝ)
    {B : ℕ → ℝ} (hB : ∀k,0 ≤ B k) (n j : ℕ) : 0 ≤ iterEnergyBudget K C D B n j := by
  induction n generalizing j with
  | zero => exact hB j
  | succ n ih => exact adjointEnergyBudget_nonneg hK D (fun k => productEnergyBudget_nonneg ih k) j

lemma iterTensorLie_polySmooth {S : Type} {d : ℕ} {H : Point d → ℝ} (hH : PolySmooth H)
    (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (F : (S → Fin d) → Point d → ℝ)
    (hA : ∀c,PolySmooth (A c)) (hF : ∀c,PolySmooth (F c)) (n : ℕ) (c : S → Fin d) :
    PolySmooth (iterTensorLie H A F n c) := by
  induction n generalizing c with
  | zero => exact hF c
  | succ n ih => exact tensorLie_polySmooth hH A _ hA ih c

theorem iterTensorLie_energy {S : Type} [Fintype S] {d : ℕ}
    {H : Point d → ℝ} (hH : PolySmooth H) (ht : HasGaussianLowerTail H)
    {K : ℝ≥0} (hL : LipschitzWith K (gradient H))
    (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (F : (S → Fin d) → Point d → ℝ)
    (hA : ∀c,PolySmooth (A c)) (hF : ∀c,PolySmooth (F c))
    (C D B : ℕ → ℝ) {α κ ρ : ℝ} (hκ : 0 ≤ κ) (hρ : 1 ≤ ρ) (hB : ∀k,0 ≤ B k)
    (hb : ∀k y, AllSplitBound (spatialTensor A (List.finRange k) y) (C k*α*ρ^k))
    (hs : ∀k,0<k → ∀y,AllSplitBound (spatialTensor (scoreField H) (List.finRange k) y) (D k*ρ^k))
    (he : ∀k,0<k → spatialEnergy F k (gibbs H) ≤ κ*ρ^(2*k)*B k)
    (n j : ℕ) (hj : 0<n ∨ 0<j) :
    spatialEnergy (iterTensorLie H A F n) j (gibbs H) ≤
      κ*(α^2*ρ^4)^n*ρ^(2*j)*iterEnergyBudget K C D B n j := by
  induction n generalizing j with
  | zero => simpa [iterTensorLie,iterEnergyBudget] using he j (by omega)
  | succ n ih =>
    have hn : 0 ≤ κ*(α^2*ρ^4)^n := mul_nonneg hκ (pow_nonneg (mul_nonneg (sq_nonneg α) (by positivity)) _)
    have hh := tensorLie_scaled_energy hH ht hL A (iterTensorLie H A F n) hA
      (iterTensorLie_polySmooth hH A F hA hF n) C D (iterEnergyBudget K C D B n) hn hρ
      (iterEnergyBudget_nonneg K.2 C D hB n) hb hs (fun k hk => ih k (Or.inr hk)) j
    apply hh.trans_eq
    dsimp [iterEnergyBudget]
    rw [show 2*(j+2)=2*j+4 by omega,pow_add,pow_succ]
    ring

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators
open TensorEnergy

def skewLieField {d : ℕ} (H : Point d → ℝ)
    (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (y : Point d) : Point d :=
  ∑z : Fin d,(∑i : Fin d,adjointCoordinate H (EuclideanSpace.basisFun (Fin d) ℝ i)
    (A (Sum.elim (fun _ => i) (fun _ => z))) y) • EuclideanSpace.basisFun (Fin d) ℝ z

lemma lieInside_apply {S : Type} {d : ℕ} (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ)
    (F : (S → Fin d) → Point d → ℝ) (c : S → Fin d) (i : Fin d) (y : Point d) :
    lieInside A F (Sum.elim c (fun _ => i)) y=
      ∑z : Fin d,A (Sum.elim (fun _ => i) (fun _ => z)) y*
        directional (EuclideanSpace.basisFun (Fin d) ℝ z) (F c) y := rfl

lemma adjointCoordinate_sum {d : ℕ} {ι : Type*} [Fintype ι] (H : Point d → ℝ)
    (v : Point d) (f : ι → Point d → ℝ) (hf : ∀i,Differentiable ℝ (f i)) :
    adjointCoordinate H v (fun y => ∑i,f i y)=fun y => ∑i,adjointCoordinate H v (f i) y := by
  unfold adjointCoordinate
  rw [directional_sum _ (fun i _ => hf i)]
  funext y
  simp only [Finset.sum_add_distrib,Finset.sum_neg_distrib,Finset.mul_sum]

lemma adjointCoordinate_mul {d : ℕ} (H : Point d → ℝ) (v : Point d)
    {f g : Point d → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    adjointCoordinate H v (fun y => f y*g y)=fun y =>
      adjointCoordinate H v f y*g y-f y*directional v g y := by
  unfold adjointCoordinate
  rw [directional_mul hf hg]
  funext y
  ring

lemma tensorLie_eq_directional {S : Type} {d : ℕ} (H : Point d → ℝ)
    (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (F : (S → Fin d) → Point d → ℝ)
    (hA : ∀c,ContDiff ℝ (⊤:ℕ∞) (A c)) (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c))
    (hsk : ∀i z y,A (Sum.elim (fun _ => i) (fun _ => z)) y=
      -A (Sum.elim (fun _ => z) (fun _ => i)) y) (c : S → Fin d) (y : Point d) :
    tensorLie H A F c y=directional (skewLieField H A y) (F c) y := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hess : (∑i : Fin d,∑z : Fin d,A (Sum.elim (fun _ => i) (fun _ => z)) y*
      directional (b i) (directional (b z) (F c)) y)=0 := by
    have he : (∑i : Fin d,∑z : Fin d,A (Sum.elim (fun _ => i) (fun _ => z)) y*
        directional (b i) (directional (b z) (F c)) y)=
        -(∑i : Fin d,∑z : Fin d,A (Sum.elim (fun _ => i) (fun _ => z)) y*
        directional (b i) (directional (b z) (F c)) y) := by
      conv_rhs => rw [Finset.sum_comm]
      rw [←Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [←Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro z _
      rw [hsk i z y,directional_commute (hF c) (b i) (b z)]
      ring
    linarith
  have hin (i : Fin d) : lieInside A F (Sum.elim c (fun _ => i))=
      fun y => ∑z : Fin d,A (Sum.elim (fun _ => i) (fun _ => z)) y*directional (b z) (F c) y := rfl
  have hadj (i : Fin d) : adjointCoordinate H (b i)
      (lieInside A F (Sum.elim c (fun _ => i))) y=
      ∑z : Fin d,(adjointCoordinate H (b i) (A (Sum.elim (fun _ => i) (fun _ => z))) y*
        directional (b z) (F c) y-A (Sum.elim (fun _ => i) (fun _ => z)) y*
        directional (b i) (directional (b z) (F c)) y) := by
    rw [hin i,adjointCoordinate_sum H (b i) (fun z y => A (Sum.elim (fun _ => i) (fun _ => z)) y*directional (b z) (F c) y) (fun z =>
      ((hA (Sum.elim (fun _ => i) (fun _ => z))).differentiable (by simp)).mul ((directional_smooth (hF c) (b z)).differentiable (by simp)))]
    apply Finset.sum_congr rfl
    intro z _
    exact congrFun (adjointCoordinate_mul H (b i) ((hA _).differentiable (by simp))
      ((directional_smooth (hF c) (b z)).differentiable (by simp))) y
  unfold tensorLie tensorAdjoint
  change (∑i : Fin d,adjointCoordinate H (b i) (lieInside A F (Sum.elim c (fun _ => i))) y)=_
  simp_rw [hadj]
  simp only [Finset.sum_sub_distrib]
  rw [hess,sub_zero,Finset.sum_comm]
  simp only [directional,skewLieField,map_sum,map_smul,smul_eq_mul,Finset.sum_mul]
  rfl

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory Set
open scoped Classical BigOperators NNReal
open TensorEnergy

lemma spatialSquared_zero {S : Type} [Fintype S] {d : ℕ}
    (F : (S → Fin d) → Point d → ℝ) (y : Point d) :
    spatialSquared F 0 y=∑c,(F c y)^2 := by
  have he : spatialTensor F (List.finRange 0) y=
      fun c => F (c ∘ (Equiv.emptySum (Fin 0) S).symm) y := rfl
  unfold spatialSquared
  rw [he]
  exact squared_reindex (fun c => F c y) (Equiv.emptySum (Fin 0) S).symm

lemma spatialEnergy_from_split {d j : ℕ} {H : Point d → ℝ}
    (hH : Continuous H) (ht : HasGaussianLowerTail H) [IsProbabilityMeasure (gibbs H)]
    (F : (Unit → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c))
    {M : ℝ} (hj : 0<j) (hb : ∀y,AllSplitBound (spatialTensor F (List.finRange j) y) M) :
    spatialEnergy F j (gibbs H) ≤ d*M^2 := by
  let : Nonempty (Fin j) := ⟨⟨0,hj⟩⟩
  have hh (y : Point d) : spatialSquared F j y≤d*M^2 :=
    (hb y).frobeniusSquared (Equiv.refl (Fin j ⊕ Unit))
  have hi := (spatialSquared_polySmooth F hF j).integrable hH ht
  exact (integral_mono hi (integrable_const _) hh).trans_eq (by simp)

theorem iteratedDerivWithin_lie {S : Type} {d : ℕ} {H : Point d → ℝ}
    (hH : PolySmooth H) (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ)
    (F : (S → Fin d) → Point d → ℝ) (hA : ∀c,PolySmooth (A c)) (hF : ∀c,PolySmooth (F c))
    (hsk : ∀i z y,A (Sum.elim (fun _ => i) (fun _ => z)) y=
      -A (Sum.elim (fun _ => z) (fun _ => i)) y)
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s) (γ : ℝ → Point d)
    (hγ : ∀t∈s,HasDerivWithinAt γ (skewLieField H A (γ t)) s t)
    (n : ℕ) (c : S → Fin d) :
    EqOn (iteratedDerivWithin n (fun t => F c (γ t)) s)
      (fun t => iterTensorLie H A F n c (γ t)) s := by
  induction n with
  | zero => intro t ht; simp [iterTensorLie]
  | succ n ih =>
    intro t ht
    rw [iteratedDerivWithin_succ]
    rw [derivWithin_congr (fun u hu => ih hu) (ih ht)]
    have hf := (iterTensorLie_polySmooth hH A F hA hF n c).smooth.differentiable (by simp)
    have hd := (hf (γ t)).hasFDerivAt.comp_hasDerivWithinAt t (hγ t ht)
    change derivWithin (iterTensorLie H A F n c ∘ γ) s t= _
    rw [hd.derivWithin (hs t ht)]
    exact (tensorLie_eq_directional H A (iterTensorLie H A F n)
      (fun c => (hA c).smooth) (fun c => (iterTensorLie_polySmooth hH A F hA hF n c).smooth)
      hsk c (γ t)).symm

theorem stationary_lie_energy {S : Type} [Fintype S] {d : ℕ} {H : Point d → ℝ}
    (hH : PolySmooth H) (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ)
    (F : (S → Fin d) → Point d → ℝ) (hA : ∀c,PolySmooth (A c)) (hF : ∀c,PolySmooth (F c))
    (hsk : ∀i z y,A (Sum.elim (fun _ => i) (fun _ => z)) y=
      -A (Sum.elim (fun _ => z) (fun _ => i)) y)
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s) (Ψ : Point d → ℝ → Point d)
    (hΨ : ∀y t,t∈s → HasDerivWithinAt (Ψ y) (skewLieField H A (Ψ y t)) s t)
    {t : ℝ} (ht : t∈s) (hc : Measurable (fun y => Ψ y t))
    (hlaw : (gibbs H).map (fun y => Ψ y t)=gibbs H) (n : ℕ) :
    (∫y,∑c,(iteratedDerivWithin n (fun u => F c (Ψ y u)) s t)^2 ∂gibbs H)=
      spatialEnergy (iterTensorLie H A F n) 0 (gibbs H) := by
  have hi : (fun y => ∑c,(iteratedDerivWithin n (fun u => F c (Ψ y u)) s t)^2)=
      fun y => spatialSquared (iterTensorLie H A F n) 0 (Ψ y t) := by
    funext y
    rw [spatialSquared_zero]
    apply Finset.sum_congr rfl
    intro c _
    rw [iteratedDerivWithin_lie hH A F hA hF hsk hs (Ψ y) (hΨ y) n c ht]
  rw [hi]
  have hm : AEStronglyMeasurable (spatialSquared (iterTensorLie H A F n) 0)
      ((gibbs H).map (fun y => Ψ y t)) :=
    (spatialSquared_polySmooth _ (iterTensorLie_polySmooth hH A F hA hF n) 0).smooth.continuous.aestronglyMeasurable
  exact (integral_map hc.aemeasurable hm).symm.trans (by rw [hlaw]; rfl)

theorem stationary_time_derivative_squared {S : Type} [Fintype S] {d : ℕ}
    {H : Point d → ℝ} (hH : PolySmooth H) (htail : HasGaussianLowerTail H)
    {K : ℝ≥0} (hL : LipschitzWith K (gradient H))
    (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (F : (S → Fin d) → Point d → ℝ)
    (hA : ∀c,PolySmooth (A c)) (hF : ∀c,PolySmooth (F c))
    (hsk : ∀i z y,A (Sum.elim (fun _ => i) (fun _ => z)) y=
      -A (Sum.elim (fun _ => z) (fun _ => i)) y)
    (C D B : ℕ → ℝ) {α κ ρ : ℝ} (hκ : 0 ≤ κ) (hρ : 1 ≤ ρ) (hB : ∀k,0 ≤ B k)
    (hb : ∀k y,AllSplitBound (spatialTensor A (List.finRange k) y) (C k*α*ρ^k))
    (hs : ∀k,0<k → ∀y,AllSplitBound (spatialTensor (scoreField H) (List.finRange k) y) (D k*ρ^k))
    (he : ∀k,0<k → spatialEnergy F k (gibbs H) ≤ κ*ρ^(2*k)*B k)
    {s : Set ℝ} (hset : UniqueDiffOn ℝ s) (Ψ : Point d → ℝ → Point d)
    (hΨ : ∀y t,t∈s → HasDerivWithinAt (Ψ y) (skewLieField H A (Ψ y t)) s t)
    {t : ℝ} (ht : t∈s) (hc : Measurable (fun y => Ψ y t))
    (hlaw : (gibbs H).map (fun y => Ψ y t)=gibbs H) {n : ℕ} (hn : 0<n) :
    (∫y,∑c,(iteratedDerivWithin n (fun u => F c (Ψ y u)) s t)^2 ∂gibbs H)≤
      κ*(α^2*ρ^4)^n*iterEnergyBudget K C D B n 0 := by
  rw [stationary_lie_energy hH A F hA hF hsk hset Ψ hΨ ht hc hlaw]
  simpa only [Nat.mul_zero,pow_zero,mul_one] using
    iterTensorLie_energy hH htail hL A F hA hF C D B hκ hρ hB hb hs he n 0 (Or.inl hn)

end LogConcaveSampling

end

end

end

end OAI
