import OAI.Analysis.AncientFlat.Regularity.NestedEstimate
import OAI.Analysis.AncientFlat.Regularity.GeometricAbsorption

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace ParabolicLocalization
open ParabolicInterior ParabolicInterpolation
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem interior_fourth_seminorm (α κ K : ℝ) (hα : 0<α) (hα1 : α<1)
    (hκ : 0<κ) (hK : 0≤K) :
    ∃ C : ℝ, 0<C ∧ ∀ (a : V × ℝ → ℝ) (b : V × ℝ → ℂ),
      HolderBound α (cylinder 2) a K → HolderBound α (cylinder 2) b K →
      (∀ p∈cylinder 2, κ≤a p) →
      ∀ (u ut f : ℝ → V → ℂ) (F U : ℝ), 0≤F → 0≤U →
      (∀ t, ContDiff ℝ 4 (u t)) →
      (∀ p∈cylinder 2, HasDerivAt (fun t => u t p.1) (ut p.2 p.1) p.2) →
      (∃ M, 0≤M ∧ JetBound α (cylinder 2) u ut M) →
      HolderBound α (cylinder 2) (fun p => f p.2 p.1) F → (∀ p∈cylinder 2, ‖u p.2 p.1‖≤U) →
      (∀ p∈cylinder 2, ut p.2 p.1+(a p : ℂ)*Δ (Δ (u p.2)) p.1+b p*u p.2 p.1=f p.2 p.1) →
      ∀ p∈cylinder (5/4), ∀ z∈cylinder (5/4),
        ‖iteratedFDeriv ℝ 4 (u p.2) p.1-iteratedFDeriv ℝ 4 (u z.2) z.1‖≤(C*(F+U))*pdist p z^α := by
  obtain ⟨C,hC,Hnest⟩ := nested_fourth_estimate (V := V) α κ K (1/64) hα hα1 hκ hK (by norm_num)
  refine ⟨65536*C,by positivity,?_⟩
  intro a b ha hb hell u ut f F U hF hU hs hd hj hf hu he
  obtain ⟨M,hM,hj⟩ := hj
  let r : ℕ → ℝ := fun n => 3/2-(1/4)*(1/2)^n
  have hr0 : r 0=5/4 := by norm_num [r]
  have hr (n : ℕ) : 1≤r n ∧ r n≤3/2 := by
    have hp : 0≤(1/2:ℝ)^n := by positivity
    have hq : (1/2:ℝ)^n≤1 := pow_le_one₀ (by norm_num) (by norm_num)
    dsimp [r]; constructor <;> linarith
  have hgap (n : ℕ) : r (n+1)-r n=(1/8)*(1/2:ℝ)^n := by dsimp [r]; rw [pow_succ]; ring
  have hlt (n : ℕ) : r n<r (n+1) := by
    have hp : 0<(1/8:ℝ)*(1/2:ℝ)^n := by positivity
    have := hgap n
    linarith
  have hsub (n : ℕ) : (cylinder (r n) : Set (V × ℝ))⊆cylinder 2 :=
    cylinder_mono (by linarith [(hr n).1]) (by linarith [(hr n).2])
  let D := fun p : V × ℝ => iteratedFDeriv ℝ 4 (u p.2) p.1
  have hold (n : ℕ) : ∀ p∈cylinder (r n), ∀ z∈cylinder (r n), ‖D p-D z‖≤M*pdist p z^α :=
    fun p hp z hz => (hj.1 4 le_rfl).2 p (hsub n hp) z (hsub n hz)
  let s : ℕ → ℝ := fun n => seminorm α (cylinder (r n)) D
  have hsM (n : ℕ) : s n≤M := seminorm_le hM (hold n)
  have hs0 (n : ℕ) : 0≤ s n := seminorm_nonneg hM (hold n)
  have hsB (n : ℕ) : ∀ p∈cylinder (r n), ∀ z∈cylinder (r n), ‖D p-D z‖≤ s n*pdist p z^α :=
    seminorm_bound hM (hold n)
  have hrec (n : ℕ) : s n≤(1/64)*s (n+1)+(32768*C*(F+U))*32^n := by
    have hh := Hnest (r n) (r (n+1)) (hr n).1 (hlt n) (hr (n+1)).2 a b
      (ha.restrict (hsub (n+1))) (hb.restrict (hsub (n+1)))
      (fun p hp => hell p (hsub (n+1) hp)) u ut f F U (s (n+1)) hF hU (hs0 (n+1)) hs
      (fun p hp => hd p (hsub (n+1) hp))
      ⟨M,hM,fun j hj' => (hj.1 j hj').restrict (hsub (n+1)),hj.2.restrict (hsub (n+1))⟩
      (hf.restrict (hsub (n+1))) (fun p hp => hu p (hsub (n+1) hp)) (hsB (n+1))
      (fun p hp => he p (hsub (n+1) hp))
    have hpow : (r (n+1)-r n)^5=(1/32768:ℝ)*(1/32:ℝ)^n := by
      rw [hgap,mul_pow,←pow_mul,show n*5=5*n by omega,pow_mul]; norm_num
    have hcan : (1/32:ℝ)^n*32^n=1 := by rw [←mul_pow]; norm_num
    have hdiv : C/(r (n+1)-r n)^5=32768*C*32^n := by
      apply (div_eq_iff (pow_ne_zero _ (sub_pos.mpr (hlt n)).ne')).mpr
      rw [hpow]
      calc
        _=C*((1/32:ℝ)^n*32^n) := by rw [hcan]; ring
        _=_ := by ring
    rw [hdiv] at hh
    have hsn := hs0 (n+1)
    have Hs := seminorm_le (show 0≤(1/64)*s (n+1)+(32768*C*32^n)*(F+U) by positivity) hh
    exact Hs.trans_eq (by ring)
  have hfinal := bounded_geometric_absorption s M (32768*C*(F+U)) (by positivity) hsM hrec
  have hfinal : s 0≤65536*C*(F+U) := hfinal.trans_eq (by ring)
  intro p hp z hz
  have h := hsB 0 p (by rwa [hr0]) z (by rwa [hr0])
  exact h.trans (mul_le_mul_of_nonneg_right hfinal (Real.rpow_nonneg (pdist_nonneg p z) _))
end ParabolicLocalization

end

end OAI
