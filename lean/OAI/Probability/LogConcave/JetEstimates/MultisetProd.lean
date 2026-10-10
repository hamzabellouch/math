import Mathlib
import OAI.Probability.LogConcave.Sampling.AdjointCoordinateContinuous

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace NNReal

lemma PolyC1.multisetProd {d : ℕ} {ι : Type*} (s : Multiset ι)
    {f : ι → Point d → ℝ} (hf : ∀i∈s,PolyC1 (f i)) :
    PolyC1 (fun x => (s.map (fun i => f i x)).prod) := by
  induction s using Multiset.induction_on with
  | empty => simpa using PolyC1.const (d:=d) 1
  | @cons a s ih =>
    simpa only [Multiset.map_cons,Multiset.prod_cons] using
      (hf a (Multiset.mem_cons_self _ _)).mul
        (ih (fun i hi => hf i (Multiset.mem_cons_of_mem hi)))

lemma integrable_multiset_sum {d : ℕ} {ι : Type*} (s : Multiset ι)
    {f : ι → Point d → ℝ} {μ : Measure (Point d)} (hf : ∀i∈s,Integrable (f i) μ) :
    Integrable (fun x => (s.map (fun i => f i x)).sum) μ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    simp only [Multiset.map_cons,Multiset.sum_cons]
    exact (hf a (Multiset.mem_cons_self _ _)).add
      (ih (fun i hi => hf i (Multiset.mem_cons_of_mem hi)))

lemma integral_multiset_sum {d : ℕ} {ι : Type*} (s : Multiset ι)
    {f : ι → Point d → ℝ} {μ : Measure (Point d)} (hf : ∀i∈s,Integrable (f i) μ) :
    (∫x,(s.map (fun i => f i x)).sum ∂μ)=(s.map (fun i => ∫x,f i x ∂μ)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    have hs := integrable_multiset_sum s (fun i hi => hf i (Multiset.mem_cons_of_mem hi))
    simp only [Multiset.map_cons,Multiset.sum_cons]
    rw [integral_add (hf a (Multiset.mem_cons_self _ _)) hs,
      ih (fun i hi => hf i (Multiset.mem_cons_of_mem hi))]

lemma directional_multisetProd {d : ℕ} {ι : Type*} [DecidableEq ι] (s : Multiset ι)
    {f : ι → Point d → ℝ} (hf : ∀i∈s,Differentiable ℝ (f i)) (v : Point d) :
    directional v (fun x => (s.map (fun i => f i x)).prod)=fun x =>
      (s.map (fun i => ((s.erase i).map (fun j => f j x)).prod *
        directional v (f i) x)).sum := by
  funext x
  unfold directional
  rw [fderiv_multiset_prod (fun i hi => hf i hi x)]
  have he : ∀t : Multiset (Point d →L[ℝ] ℝ), t.sum v=(t.map (fun A => A v)).sum := by
    intro t
    induction t using Multiset.induction_on with
    | empty => simp
    | @cons a t ih => simp [ih]
  rw [he,Multiset.map_map]
  rfl

theorem adjointCoordinate_mixed_product_pairing {d : ℕ} {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ] {H f : Point d → ℝ}
    {g : ι → Point d → ℝ} {r : κ → Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ 1 H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith K (gradient H)) (hf : PolyC1 f)
    (s : Finset ι) (hg : ∀j∈s,PolyC1 (g j))
    (t : Multiset κ) (hr : ∀j∈t,PolyC1 (r j)) (v : Point d) :
    (∫x,adjointCoordinate H v f x*(∏j∈s,g j x)*(t.map (fun k => r k x)).prod ∂gibbs H)=
      (∑j∈s,∫x,f x*directional v (g j) x*(∏k∈s.erase j,g k x)*
        (t.map (fun k => r k x)).prod ∂gibbs H)+
      (t.map (fun j => ∫x,f x*(∏k∈s,g k x)*directional v (r j) x*
        ((t.erase j).map (fun k => r k x)).prod ∂gibbs H)).sum := by
  let G := fun x => ∏j∈s,g j x
  let R := fun x => (t.map (fun j => r j x)).prod
  have hG : PolyC1 G := PolyC1.prod s hg
  have hR : PolyC1 R := PolyC1.multisetProd t hr
  have hiG : Integrable (fun x => f x*directional v G x*R x) (gibbs H) :=
    integrable_polynomial_gibbs hH.continuous ht
      ((hf.continuous.mul (hG.directional_continuous v)).mul hR.continuous)
      ((Appell.HasGrowth.mul hf.growth (hG.derivative_growth v)).mul hR.growth)
  have hiR : Integrable (fun x => f x*G x*directional v R x) (gibbs H) :=
    integrable_polynomial_gibbs hH.continuous ht
      ((hf.continuous.mul hG.continuous).mul (hR.directional_continuous v))
      ((Appell.HasGrowth.mul hf.growth hG.growth).mul (hR.derivative_growth v))
  change (∫x,adjointCoordinate H v f x*G x*R x ∂gibbs H)=_
  simp_rw [mul_assoc (adjointCoordinate H v f _) (G _) (R _)]
  rw [adjointCoordinate_pairing hH ht hL hf (hG.mul hR) v,
    directional_mul hG.differentiable hR.differentiable]
  simp_rw [mul_add,mul_assoc]
  rw [integral_add (by simpa only [mul_assoc] using hiG)
    (by simpa only [mul_assoc] using hiR)]
  congr 1
  · change (∫x,f x*(directional v (fun x => ∏j∈s,g j x) x*R x) ∂gibbs H)=_
    rw [directional_prod s (fun j hj => (hg j hj).differentiable)]
    simp_rw [Finset.sum_mul,Finset.mul_sum]
    have hi (j : ι) (hj : j∈s) : Integrable (fun x =>
        f x*((∏k∈s.erase j,g k x)*directional v (g j) x*R x)) (gibbs H) := by
      have hp := PolyC1.prod (s.erase j) (fun k hk => hg k (Finset.mem_of_mem_erase hk))
      exact integrable_polynomial_gibbs hH.continuous ht
        (hf.continuous.mul ((hp.continuous.mul ((hg j hj).directional_continuous v)).mul hR.continuous))
        (Appell.HasGrowth.mul hf.growth (Appell.HasGrowth.mul (Appell.HasGrowth.mul hp.growth ((hg j hj).derivative_growth v)) hR.growth))
    rw [integral_finsetSum s hi]
    apply Finset.sum_congr rfl
    intro j hj
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [R]
    ring
  · change (∫x,f x*(G x*directional v (fun x => (t.map (fun k => r k x)).prod) x) ∂gibbs H)=_
    rw [directional_multisetProd t (fun j hj => (hr j hj).differentiable)]
    have he : (fun x => f x*(G x*(t.map (fun j => ((t.erase j).map (fun k => r k x)).prod*
        directional v (r j) x)).sum))=fun x =>
        (t.map (fun j => f x*G x*directional v (r j) x*
          ((t.erase j).map (fun k => r k x)).prod)).sum := by
      funext x
      rw [←Multiset.sum_map_mul_left,←Multiset.sum_map_mul_left]
      apply congrArg Multiset.sum
      apply Multiset.map_congr rfl
      intro j hj
      ring
    rw [he]
    have hhi : ∀j∈t,Integrable (fun x => f x*G x*directional v (r j) x*
        ((t.erase j).map (fun k => r k x)).prod) (gibbs H) := by
      intro j hj
      have hp := PolyC1.multisetProd (t.erase j) (fun k hk => hr k (Multiset.mem_of_mem_erase hk))
      exact integrable_polynomial_gibbs hH.continuous ht
        (((hf.continuous.mul hG.continuous).mul ((hr j hj).directional_continuous v)).mul hp.continuous)
        (Appell.HasGrowth.mul (Appell.HasGrowth.mul (Appell.HasGrowth.mul hf.growth hG.growth) ((hr j hj).derivative_growth v)) hp.growth)
    simpa only [G,mul_assoc] using integral_multiset_sum t hhi
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
