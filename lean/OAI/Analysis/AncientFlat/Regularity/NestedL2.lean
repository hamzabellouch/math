import OAI.Analysis.AncientFlat.Evolution.BoxOscillation

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Laplacian
namespace ParabolicLocalization
open ParabolicInterior ParabolicAverage
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

lemma nested_l2_sup (α κ K θ : ℝ) (hα : 0<α) (hα1 : α<1)
    (hκ : 0<κ) (hK : 0≤K) (hθ : 0<θ) :
    ∃ C : ℝ, 0<C ∧ ∀ (r R : ℝ), 1≤r → r<R → R≤2 →
      ∀ (a : V × ℝ → ℝ) (b : V × ℝ → ℂ),
      HolderBound α (cylinder R) a K → HolderBound α (cylinder R) b K → (∀ p∈cylinder R, κ≤a p) →
      ∀ (u ut f : ℝ → V → ℂ) (F U N : ℝ), 0≤F → 0≤U → 0≤N →
      (∀ t, ContDiff ℝ 4 (u t)) →
      (∀ p∈cylinder R, HasDerivAt (fun t => u t p.1) (ut p.2 p.1) p.2) →
      (∃ M, 0≤M ∧ JetBound α (cylinder R) u ut M) →
      HolderBound α (cylinder R) (fun p => f p.2 p.1) F → (∀ p∈cylinder R, ‖u p.2 p.1‖≤U) →
      eLpNorm (fun p : V × ℝ => u p.2 p.1) 2 ((volume.prod volume).restrict (cylinder R))≤ENNReal.ofReal N →
      (∀ p∈cylinder R, ut p.2 p.1+(a p : ℂ)*Δ (Δ (u p.2)) p.1+b p*u p.2 p.1=f p.2 p.1) →
      ∀ p∈cylinder r, ‖u p.2 p.1‖≤θ*U+(C/(R-r)^(4*(Module.finrank ℝ V+4)))*(F+N) := by
  obtain ⟨D,hD,Hder⟩ := nested_derivative_sup (V := V) α κ K hα hα1 hκ hK
  obtain ⟨A,hA,Hav⟩ := exists_averaging_constant (V := V)
  let d := Module.finrank ℝ V+4
  let η := min (1/4) (θ/(32*D))
  have hη : 0<η := lt_min (by norm_num) (by positivity)
  have hη1 : η≤1/4 := min_le_left _ _
  have hηθ : 32*D*η≤θ := by
    have := min_le_right (1/4:ℝ) (θ/(32*D))
    exact (mul_comm (32*D) η) ▸ ((le_div_iff₀ (by positivity : 0<32*D)).mp this)
  let C := θ+A/η^d+1
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro r R hr hrR hR a b ha hb hell u ut f F U N hF hU hN hs hd hj hf hu hLp he p hp
  let g := R-r
  let m := (r+R)/2
  let q := η*g^4
  have hg : 0<g := sub_pos.mpr hrR
  have hg1 : g≤1 := by dsimp [g]; linarith
  have hq : 0<q := by dsimp [q]; positivity
  have hg4 : g^4≤g := by simpa using pow_le_pow_of_le_one hg.le hg1 (by norm_num : (1:ℕ)≤4)
  have hqg : q≤g/4 := by dsimp [q]; nlinarith
  have hq1 : q≤1 := by linarith
  have hm : 1≤ m := by dsimp [m]; linarith
  have hmR : m<R := by dsimp [m]; linarith
  have hmg : R-m=g/2 := by dsimp [m,g]; ring
  have hgap : r+q≤ m := by dsimp [m,g] at *; linarith
  let B := (16*D/g^4)*(F+U)
  have hB : 0≤B := by dsimp [B]; positivity
  have Hmid := Hder m R hm hmR hR a b ha hb hell u ut f F U hF hU hs hd hj hf hu he
  have heq : D/(R-m)^4=16*D/g^4 := by rw [hmg]; field_simp; ring
  simp only [heq] at Hmid
  have hsub : (cylinder m : Set (V × ℝ))⊆cylinder R := cylinder_mono (by linarith) hmR.le
  have Hosc := box_oscillation r m q B (by linarith) hq hq1 hgap hB u ut hs
    (fun p hp => hd p (hsub hp)) (fun p hp => (Hmid p hp).1 1 (by norm_num))
    (fun p hp => (Hmid p hp).2) p hp
  have Havg := Hav p q hq hq1 (cylinder R)
    ((box_subset_cylinder r m q (by linarith) hq hgap p hp).trans hsub)
    (fun p => u p.2 p.1) N (2*B*q) hN (by positivity) hLp Hosc
  have hE : 2*B*q≤θ*(F+U) := by
    have hid : 2*B*q=(32*D*η)*(F+U) := by dsimp [B,q]; field_simp; ring
    rw [hid]
    exact mul_le_mul_of_nonneg_right hηθ (add_nonneg hF hU)
  have hqd : q^d=η^d*g^(4*d) := by dsimp [q]; rw [mul_pow,pow_mul]
  have hcoef : A/q^d=(A/η^d)/g^(4*d) := by rw [hqd]; ring_nf
  have hgp : 0<g^(4*d) := pow_pos hg _
  have hgp1 : g^(4*d)≤1 := pow_le_one₀ hg.le hg1
  have hCθ : θ≤C/g^(4*d) := by
    apply (le_div_iff₀ hgp).mpr
    have hcθ : θ≤C := by dsimp [C]; linarith [div_nonneg hA.le (pow_nonneg hη.le d)]
    exact (mul_le_of_le_one_right hθ.le hgp1).trans hcθ
  have hCA : (A/η^d)/g^(4*d)≤C/g^(4*d) := by
    apply div_le_div_of_nonneg_right _ hgp.le
    dsimp [C]; linarith
  calc
    ‖u p.2 p.1‖≤θ*(F+U)+((A/η^d)/g^(4*d))*N := Havg.trans (by rw [hcoef]; linarith)
    _≤θ*U+(C/g^(4*d))*(F+N) := by
      nlinarith [mul_le_mul_of_nonneg_right hCθ hF,mul_le_mul_of_nonneg_right hCA hN]
end ParabolicLocalization

end

end OAI
