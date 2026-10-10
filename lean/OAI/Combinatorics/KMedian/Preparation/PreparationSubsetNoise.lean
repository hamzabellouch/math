import Mathlib
import OAI.Combinatorics.KMedian.Preparation.PreparationStars
import OAI.Combinatorics.KMedian.Preparation.PreparationRescaling
import OAI.Combinatorics.KMedian.Geometry.FilteredMoments
import OAI.Combinatorics.KMedian.Preparation.PreparationNoise

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {I T Ω Ξ : Type} [Fintype I] [DecidableEq I]
  [Fintype T] [DecidableEq T] [Fintype Ω] [Fintype Ξ]

omit [Fintype Ω] in

theorem bundle_subset_moments (μ : FiniteLaw Ξ) (Y : Ξ → T × I → ℝ)
    (P : T → Finset I) (y : I → ℝ) (p p' : T → ℝ) (F : Finset I) (g : ℝ)
    (hm : ∀ t i, μ.expect (fun ξ => Y ξ (t,i))=if i ∈ P t then p' t*y i/p t else 0)
    (hv : ∀ a, μ.variance (fun ξ => Y ξ a) ≤ g*(if a.2 ∈ P a.1 then p' a.1*y a.2/p a.1 else 0))
    (hc : ∀ a b, a ≠ b → μ.expect (fun ξ => Y ξ a*Y ξ b) ≤
      (if a.2 ∈ P a.1 then p' a.1*y a.2/p a.1 else 0)*
      (if b.2 ∈ P b.1 then p' b.1*y b.2/p b.1 else 0)) :
    μ.expect (fun ξ => ∑ t, ∑ i ∈ F, Y ξ (t,i))=
      (∑ t, (∑ i ∈ F ∩ P t, y i)*p' t/p t) ∧
    μ.variance (fun ξ => ∑ t, ∑ i ∈ F, Y ξ (t,i)) ≤
      g*(∑ t, (∑ i ∈ F ∩ P t, y i)*p' t/p t) := by
  classical
  let A : Finset (T × I) := univ.filter (fun a => a.2 ∈ F)
  let m : T × I → ℝ := fun a => if a.2 ∈ P a.1 then p' a.1*y a.2/p a.1 else 0
  have he := μ.restricted_moments Y m A (fun a => hm a.1 a.2) hv hc
  have hs : ∀ ξ, (∑ a ∈ A, Y ξ a)=∑ t, ∑ i ∈ F, Y ξ (t,i) := by
    intro ξ
    simp only [A,sum_filter,Fintype.sum_prod_type,sum_ite_mem,univ_inter]
  have hs' : (∑ a ∈ A, m a)=∑ t, (∑ i ∈ F ∩ P t, y i)*p' t/p t := by
    simp only [A,m,sum_filter,Fintype.sum_prod_type,sum_ite_mem,univ_inter,← sum_div,← mul_sum]
    apply sum_congr rfl
    intro t _
    ring
  simpa only [hs,hs'] using he

theorem preparation_shortfall (ν : FiniteLaw Ω) (κ : Ω → FiniteLaw Ξ)
    (P : T → Finset I) (y : I → ℝ) (p c : T → ℝ)
    (p' : Ω → T → ℝ) (Z : T → Ω → ℝ)
    (U : Ω → I → ℝ) (Y : Ω → Ξ → T × I → ℝ)
    (F : Finset I) {g γ p₀ : ℝ}
    (hg : 0 ≤ g) (hγ : 0 ≤ γ) (hp₀ : 0 < p₀)
    (hy : ∀ i, 0 ≤ y i) (hF : ∑ i ∈ F, y i=1)
    (hP : Pairwise (fun s t => Disjoint (P s) (P t)))
    (hp : ∀ t, p₀ ≤ p t) (hpc : ∀ t, p t=1-c t)
    (hc0 : ∀ t, 0 ≤ c t) (hc1 : ∀ t, c t ≤ 1/2)
    (hp' : ∀ ω t, p' ω t=1-min (Z t ω) (1/2))
    (hcap : ∀ ω t, p' ω t ≤ 1)
    (hZm : ∀ t, ν.expect (Z t)=(1+γ)*c t)
    (hZv : ∀ t, ν.variance (Z t) ≤ g*(1+γ)*c t)
    (hUm : ∀ i, ν.expect (fun ω => U ω i)=y i)
    (hUv : ∀ i, ν.variance (fun ω => U ω i) ≤ g*y i)
    (hUc : ∀ i j, i ≠ j → ν.expect (fun ω => U ω i*U ω j) ≤ y i*y j)
    (hYm : ∀ ω t i, (κ ω).expect (fun ξ => Y ω ξ (t,i))=
      if i ∈ P t then p' ω t*y i/p t else 0)
    (hYv : ∀ ω a, (κ ω).variance (fun ξ => Y ω ξ a) ≤
      g*(if a.2 ∈ P a.1 then p' ω a.1*y a.2/p a.1 else 0))
    (hYc : ∀ ω a b, a ≠ b → (κ ω).expect (fun ξ => Y ω ξ a*Y ω ξ b) ≤
      (if a.2 ∈ P a.1 then p' ω a.1*y a.2/p a.1 else 0)*
      (if b.2 ∈ P b.1 then p' ω b.1*y b.2/p b.1 else 0)) :
    (ν.joint κ).expect (fun z => max
      (1-(∑ i ∈ F ∩ SupplierStars.outside P, U z.1 i)-(∑ t, ∑ i ∈ F, Y z.1 z.2 (t,i))) 0)
      ≤ Real.sqrt g+Real.sqrt (g/p₀)+(γ+Real.sqrt (g*(1+γ)))/p₀ := by
  classical
  let a := fun t => ∑ i ∈ F ∩ P t, y i
  let u := ∑ i ∈ F ∩ SupplierStars.outside P, y i
  have ha : ∀ t, 0 ≤ a t := fun t => sum_nonneg (fun i _ => hy i)
  have hu : 0 ≤ u := sum_nonneg (fun i _ => hy i)
  have hpart : u+(∑ t, a t)=1 := (SupplierStars.mass_partition y P hP F).trans hF
  have has : ∑ t, a t ≤ 1 := by linarith only [hpart,hu]
  have hu1 : u ≤ 1 := by linarith only [hpart,sum_nonneg (fun t (_ : t ∈ univ) => ha t)]
  obtain ⟨hmean,hvar⟩ := ν.restricted_moments U y (F ∩ SupplierStars.outside P) hUm hUv hUc
  have hvar' : ν.variance (fun ω => ∑ i ∈ F ∩ SupplierStars.outside P, U ω i) ≤ g :=
    hvar.trans ((mul_le_mul_of_nonneg_left hu1 hg).trans_eq (mul_one _))
  have hbundle := fun ω => bundle_subset_moments (κ ω) (Y ω) P y p (p' ω) F g
    (hYm ω) (hYv ω) (hYc ω)
  have hB : ν.expect (fun ω => |(∑ t, a t*p' ω t/p t)-(∑ t, a t)|) ≤
      (γ+Real.sqrt (g*(1+γ)))/p₀ := by
    apply rescaling_total_noise ν a p p' hp₀ ha has hp (by positivity)
    intro t
    have he := clipped_bundle_noise ν (Z t) (hc0 t) (hc1 t) hγ hg (hZm t) (hZv t)
    simpa only [← hpc t,← hp'] using he
  apply conditional_shortfall ν κ
    (fun ω => ∑ i ∈ F ∩ SupplierStars.outside P, U ω i)
    (fun ω => ∑ t, a t*p' ω t/p t)
    (fun ω ξ => ∑ t, ∑ i ∈ F, Y ω ξ (t,i)) hpart hmean hvar'
    (fun ω => (hbundle ω).1) _ hB
  intro ω
  calc
    _ ≤ g*(∑ t, a t*p' ω t/p t) := (hbundle ω).2
    _ ≤ g*(1/p₀) := mul_le_mul_of_nonneg_left
      (rescaled_mass_bound a p (p' ω) hp₀ ha has hp (hcap ω)) hg
    _ = g/p₀ := by ring

end MetricKMedian.Preparation
end
end

end OAI
