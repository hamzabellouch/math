import OAI.Geometry.NodalSets.Elliptic.EnvelopeRegion
import OAI.Geometry.NodalSets.Waves.EuclideanGaussianSmallBall
import OAI.Geometry.NodalSets.Waves.GaussianJet

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability
noncomputable section

def firstJetSize (f : Coord → ℝ) (N : ℝ) (x : Coord) : ℝ :=
  |f x|+N⁻¹*‖fderiv ℝ f x‖

lemma firstJetSize_nonneg (f : Coord → ℝ) {N : ℝ} (hN : 0 ≤ N) (x : Coord) :
    0 ≤ firstJetSize f N x := by unfold firstJetSize; positivity

lemma normalizedRealJet_norm_le (f : Coord → ℝ) (S : ℝ) (x : Coord)
    {N : ℝ} (hN : 0 ≤ N) :
    ‖normalizedRealJet f N S x‖ ≤ 6*Real.exp (-N*S)*firstJetSize f N x := by
  let v : Fin 5 → ℝ := Fin.cons (Real.exp (-N*S)*f x)
    (fun i : Fin 4 ↦ Real.exp (-N*S)*N⁻¹*fderiv ℝ f x (Pi.single i 1))
  have hb : ‖v‖ ≤ Real.exp (-N*S)*firstJetSize f N x := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Real.exp_pos _).le (firstJetSize_nonneg f hN x))).mpr
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · change |Real.exp (-N*S)*f x| ≤ _
      rw [abs_mul,abs_of_pos (Real.exp_pos _)]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact le_add_of_nonneg_right (by positivity)
    · change |Real.exp (-N*S)*N⁻¹*fderiv ℝ f x (Pi.single j 1)| ≤ _
      rw [abs_mul,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_nonneg (inv_nonneg.mpr hN),mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      have hj : |fderiv ℝ f x (Pi.single j 1)| ≤ ‖fderiv ℝ f x‖ := by
        simpa [Pi.norm_single] using (fderiv ℝ f x).le_opNorm (Pi.single j (1:ℝ))
      exact (mul_le_mul_of_nonneg_left hj (inv_nonneg.mpr hN)).trans
        (le_add_of_nonneg_left (abs_nonneg _))
  have h := euclidean_toLp_norm_le v
  norm_num at h
  exact h.trans (by change 6*‖v‖ ≤ _; nlinarith)

lemma firstJetSize_sub_le (f g : Coord → ℝ) {N : ℝ} (hN : 0 ≤ N) (x : Coord)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    firstJetSize (fun z ↦ f z-g z) N x ≤ firstJetSize f N x+firstJetSize g N x := by
  unfold firstJetSize
  rw [fderiv_fun_sub hf hg]
  have h := mul_le_mul_of_nonneg_left (norm_sub_le (fderiv ℝ f x) (fderiv ℝ g x))
    (inv_nonneg.mpr hN)
  nlinarith [abs_sub (f x) (g x)]

lemma firstJetSize_seed_dominance (seed W : Coord → ℝ) {N : ℝ} (hN : 0 ≤ N)
    (x : Coord) (hs : DifferentiableAt ℝ seed x) (hW : DifferentiableAt ℝ W x)
    {c E : ℝ} (hseed : c*E ≤ firstJetSize seed N x)
    (hrandom : firstJetSize W N x ≤ (c/2)*E) :
    (c/2)*E ≤ firstJetSize (fun z ↦ seed z+W z) N x := by
  have h := firstJetSize_sub_le (fun z ↦ seed z+W z) W hN x (hs.fun_add hW) hW
  have he : (fun z ↦ (seed z+W z)-W z) = seed := by funext z; ring
  rw [he] at h
  linarith

lemma high_region_firstJetSize_lower {Ω : Set Coord} {S S0 : Coord → ℝ}
    {n : ℕ} (hn : 24 ≤ n) {x : Coord} (hx : x ∈ highEnvelopeRegion Ω S S0 n)
    (f : Coord → ℝ) (hjet : ((n:ℝ)^56)⁻¹ ≤ ‖normalizedRealJet f n (S x) x‖) :
    (4*((n:ℝ)^65)⁻¹)*max (Real.exp ((n:ℝ)*S x)) (Real.exp ((n:ℝ)*S0 x)) ≤
      firstJetSize f n x := by
  have hnpos : 0 < n := by omega
  have hnR : (0:ℝ) < n := by exact_mod_cast hnpos
  have hn6 : (24:ℝ) ≤ n := by exact_mod_cast hn
  have h := hjet.trans (normalizedRealJet_norm_le f (S x) x hnR.le)
  have hmul := mul_le_mul_of_nonneg_right h (Real.exp_pos ((n:ℝ)*S x)).le
  have he : Real.exp (-(n:ℝ)*S x)*Real.exp ((n:ℝ)*S x) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hh : ((n:ℝ)^56)⁻¹*Real.exp ((n:ℝ)*S x) ≤ 6*firstJetSize f n x := by
    have hex : 6*Real.exp (-(n:ℝ)*S x)*firstJetSize f n x*Real.exp ((n:ℝ)*S x) =
        6*firstJetSize f n x := by
      calc
        _ = 6*(Real.exp (-(n:ℝ)*S x)*Real.exp ((n:ℝ)*S x))*firstJetSize f n x := by ring
        _ = _ := by rw [he]; ring
    rwa [hex] at hmul
  have henv := high_envelope_bound hnpos hx
  calc
    _ ≤ (4*((n:ℝ)^65)⁻¹)*((n:ℝ)^8*Real.exp ((n:ℝ)*S x)) :=
      mul_le_mul_of_nonneg_left henv (by positivity)
    _ = (4*((n:ℝ)^57)⁻¹)*Real.exp ((n:ℝ)*S x) := by field_simp
    _ ≤ firstJetSize f n x := by
      have he' : ((n:ℝ)^56)⁻¹ = (n:ℝ)*((n:ℝ)^57)⁻¹ := by field_simp
      rw [he'] at hh
      have hp := firstJetSize_nonneg f hnR.le x
      nlinarith [mul_nonneg (sub_nonneg.mpr hn6)
        (mul_nonneg (inv_nonneg.mpr (pow_nonneg hnR.le 57)) (Real.exp_pos ((n:ℝ)*S x)).le)]

end
end Yau.Geometry

end OAI
