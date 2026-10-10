import OAI.Analysis.AncientFlat.Regularity.NestedL2
import OAI.Analysis.AncientFlat.Regularity.GeneralAbsorption
import OAI.Analysis.AncientFlat.Evolution.SupNorm

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Laplacian
namespace ParabolicInterior
open ParabolicLocalization
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
theorem interior_sup_l2 (α κ K : ℝ) (hα : 0<α) (hα1 : α<1) (hκ : 0<κ) (hK : 0≤K) :
    ∃ C : ℝ, 0<C ∧ ∀ (a : V × ℝ → ℝ) (b : V × ℝ → ℂ),
      HolderBound α (cylinder 2) a K → HolderBound α (cylinder 2) b K →
      (∀ p ∈ cylinder 2, κ≤a p) →
      ∀ (u ut f : ℝ → V → ℂ) (F N : ℝ), 0≤F → 0≤N →
      (∀ t : ℝ, ContDiff ℝ 4 (u t)) →
      (∀ p ∈ cylinder 2, HasDerivAt (fun t => u t p.1) (ut p.2 p.1) p.2) →
      (∃ M : ℝ, 0≤M ∧ JetBound α (cylinder 2) u ut M) →
      HolderBound α (cylinder 2) (fun p => f p.2 p.1) F →
      eLpNorm (fun p : V × ℝ => u p.2 p.1) 2
        ((volume.prod volume).restrict (cylinder 2))≤ENNReal.ofReal N →
      (∀ p ∈ cylinder 2, ut p.2 p.1+(a p : ℂ)*Δ (Δ (u p.2)) p.1+b p*u p.2 p.1=f p.2 p.1) →
      ∀ p∈cylinder (5/4), ‖u p.2 p.1‖≤C*(F+N) := by
  let k := 4*(Module.finrank ℝ V+4)
  let B : ℝ := 2^k
  have hB : 1≤B := one_le_pow₀ (by norm_num)
  have hBp : 0<B := lt_of_lt_of_le zero_lt_one hB
  obtain ⟨C,hC,Hnest⟩ := nested_l2_sup (V := V) α κ K (1/(2*B)) hα hα1 hκ hK (by positivity)
  refine ⟨2*C*8^k,by positivity,?_⟩
  intro a b ha hb hell u ut f F N hF hN hs hd hj hf hLp he
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
  let U := fun p : V × ℝ => u p.2 p.1
  have hu (n : ℕ) : ∀ p∈cylinder (r n), ‖U p‖≤M := by
    intro p hp
    simpa only [norm_iteratedFDeriv_zero] using (hj.1 0 (by norm_num)).1 p (hsub n hp)
  let s : ℕ → ℝ := fun n => supNorm (cylinder (r n)) U
  have hsM (n : ℕ) : s n≤M := supNorm_le hM (hu n)
  have hs0 (n : ℕ) : 0≤ s n := supNorm_nonneg hM (hu n)
  have hsB (n : ℕ) : ∀ p∈cylinder (r n), ‖U p‖≤ s n := supNorm_bound hM (hu n)
  have hrec (n : ℕ) : s n≤(1/(2*B))*s (n+1)+(C*8^k*(F+N))*B^n := by
    have hh := Hnest (r n) (r (n+1)) (hr n).1 (hlt n) (by linarith [(hr (n+1)).2]) a b
      (ha.restrict (hsub (n+1))) (hb.restrict (hsub (n+1)))
      (fun p hp => hell p (hsub (n+1) hp)) u ut f F (s (n+1)) N hF (hs0 (n+1)) hN hs
      (fun p hp => hd p (hsub (n+1) hp))
      ⟨M,hM,fun j hj' => (hj.1 j hj').restrict (hsub (n+1)),hj.2.restrict (hsub (n+1))⟩
      (hf.restrict (hsub (n+1))) (hsB (n+1))
      ((eLpNorm_mono_measure _ (Measure.restrict_mono (hsub (n+1)) le_rfl)).trans hLp)
      (fun p hp => he p (hsub (n+1) hp))
    have hcan : (r (n+1)-r n)*(8*2^n)=1 := by
      rw [hgap]
      have h : (1/2:ℝ)^n*2^n=1 := by rw [←mul_pow]; norm_num
      nlinarith
    have hpow : (8*2^n:ℝ)^k=8^k*B^n := by
      rw [mul_pow]
      congr 1
      change ((2:ℝ)^n)^k=((2:ℝ)^k)^n
      rw [←pow_mul,←pow_mul,Nat.mul_comm]
    have hdiv : C/(r (n+1)-r n)^k=C*8^k*B^n := by
      apply (div_eq_iff (pow_ne_zero _ (sub_pos.mpr (hlt n)).ne')).mpr
      have hp := congrArg (fun x : ℝ => x^k) hcan
      rw [mul_pow,hpow,one_pow] at hp
      nlinarith
    change ∀ p∈cylinder (r n), ‖U p‖≤(1/(2*B))*s (n+1)+(C/(r (n+1)-r n)^k)*(F+N) at hh
    rw [hdiv] at hh
    have hsn := hs0 (n+1)
    have Hs := supNorm_le (show 0≤(1/(2*B))*s (n+1)+(C*8^k*B^n)*(F+N) by positivity) hh
    exact Hs.trans_eq (by ring)
  have hfinal := bounded_geometric_absorption_general B hB s M (C*8^k*(F+N)) (by positivity) hsM hrec
  intro p hp
  have hh := hsB 0 p (by rwa [hr0])
  exact (hh.trans hfinal).trans_eq (by ring)
end ParabolicInterior

end

end OAI
