import OAI.Geometry.PolarProducts.ExteriorHamiltonian

namespace OAI

universe u127

section NonsqueezingInline

namespace CylinderParameters
noncomputable section
open Set Filter Finset
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE
variable {κ : Type u127} [Fintype κ] [DecidableEq κ]

 def weights (j₀ : κ) (a b : ℝ) (j : κ) : ℝ := if j=j₀ then a else b

 theorem energy_weights (j₀ : κ) (a b : ℝ) (z : Vector κ) :
    energy (weights j₀ a b) z = (a-b)*‖z j₀‖^2+b*‖z‖^2 := by
   have hh (j : κ) : weights j₀ a b j*‖z j‖^2 =
       b*‖z j‖^2+(if j=j₀ then (a-b)*‖z j‖^2 else 0) := by
     by_cases hj : j=j₀ <;> simp only [weights,hj,ite_true,ite_false] <;> ring
   simp only [energy,hh,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
     ← Finset.mul_sum,← EuclideanSpace.norm_sq_eq]
   ring

 theorem energy_weights_upper (j₀ : κ) {a b R M : ℝ} (hb : 0 ≤ b) (hab : b ≤ a)
    (hR : 0 ≤ R) {z : Vector κ} (hz : ‖z‖^2 ≤ M) (hz₀ : ‖z j₀‖^2 ≤ R) :
    energy (weights j₀ a b) z ≤ a*R+b*M := by
   rw [energy_weights]
   have h1 := mul_le_mul_of_nonneg_left hz (show 0 ≤ b from hb)
   have h2 := mul_le_mul_of_nonneg_left hz₀ (sub_nonneg.mpr hab)
   nlinarith

 theorem gap_first {m : ℤ} : Real.pi/2 ≤ |Real.pi*(m:ℝ)-3*Real.pi/2| := by
   rcases le_or_gt m 1 with hm | hm
   · have hm' : (m:ℝ) ≤ 1 := by exact_mod_cast hm
     apply (le_abs.mpr (Or.inr ?_))
     nlinarith [Real.pi_pos]
   · have hm' : (2:ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
     apply (le_abs.mpr (Or.inl ?_))
     nlinarith [Real.pi_pos]

 theorem gap_small {b : ℝ} (hb : 0 < b) (hbπ : b ≤ Real.pi/2) (m : ℤ) :
    b ≤ |Real.pi*(m:ℝ)-b| := by
   rcases le_or_gt m 0 with hm | hm
   · have hm' : (m:ℝ) ≤ 0 := by exact_mod_cast hm
     apply (le_abs.mpr (Or.inr ?_))
     nlinarith [Real.pi_pos]
   · have hm' : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
     apply (le_abs.mpr (Or.inl ?_))
     nlinarith [Real.pi_pos]

omit [Fintype κ] in
 theorem weights_bounds (j₀ : κ) {b : ℝ} (hb : 0 < b) (hbπ : b ≤ Real.pi/4) :
    (∀ j, b ≤ weights j₀ (3*Real.pi/2) b j) ∧
    Real.pi+b ≤ weights j₀ (3*Real.pi/2) b j₀ ∧
    (∀ j, |weights j₀ (3*Real.pi/2) b j| ≤ 3*Real.pi/2) ∧
    (∀ j, j ≠ j₀ → weights j₀ (3*Real.pi/2) b j < Real.pi) ∧
    (∀ m : ℤ, ∀ j, b ≤ |Real.pi*(m:ℝ)-weights j₀ (3*Real.pi/2) b j|) := by
   have hab : b ≤ 3*Real.pi/2 := by linarith [Real.pi_pos]
   refine ⟨?_,?_,?_,?_,?_⟩
   · intro j; unfold weights; split_ifs
     · exact hab
     · exact le_rfl
   · simp only [weights,ite_true]; linarith [Real.pi_pos]
   · intro j; unfold weights; split_ifs
     · rw [abs_of_pos (by positivity)]
     · rw [abs_of_pos hb]; exact hab
   · intro j hj; simp only [weights,hj,ite_false]; linarith [Real.pi_pos]
   · intro m j; unfold weights; split_ifs
     · exact (show b ≤ Real.pi/2 by linarith [Real.pi_pos]).trans gap_first
     · exact gap_small hb (by linarith [Real.pi_pos]) m

 theorem exists_parameters (j₀ : κ) {R M m : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hRm : Real.pi*R < m) :
    ∃ b T δ : ℝ, 0 < b ∧ b ≤ Real.pi/4 ∧ 0 < δ ∧ 0 < T ∧
      Real.pi*(T+δ) < m*(3*Real.pi/2) ∧
      ∀ z : Vector κ, ‖z‖^2 ≤ M → ‖z j₀‖^2 ≤ R →
        energy (weights j₀ (3*Real.pi/2) b) z < T := by
   let a := 3*Real.pi/2
   have ha : 0 < a := by dsimp [a]; positivity
   let τ := (m-Real.pi*R)/(4*Real.pi)
   have hτ : 0 < τ := div_pos (sub_pos.mpr hRm) (by positivity)
   have hτeq : 4*Real.pi*τ=m-Real.pi*R := by dsimp [τ]; field_simp
   let b := min (Real.pi/4) (a*τ/(M+1))
   have hb : 0 < b := lt_min (by positivity) (div_pos (mul_pos ha hτ) (by linarith))
   have hbπ : b ≤ Real.pi/4 := min_le_left _ _
   have hbb : b*(M+1) ≤ a*τ := (le_div_iff₀ (by linarith : 0 < M+1)).mp (min_le_right _ _)
   have hbM : b*M < a*τ := by nlinarith
   refine ⟨b,a*(R+τ),a*τ,hb,hbπ,mul_pos ha hτ,mul_pos ha (by linarith),?_,?_⟩
   · change Real.pi*(a*(R+τ)+a*τ) < m*a
     have hh : Real.pi*(R+2*τ)< m := by nlinarith
     nlinarith [mul_lt_mul_of_pos_left hh ha]
   · intro z hz hz₀
     have hab : b ≤ a := by dsimp [a]; linarith [Real.pi_pos]
     have he := energy_weights_upper j₀ hb.le hab hR hz hz₀
     change energy (weights j₀ a b) z < a*(R+τ)
     nlinarith

end
end CylinderParameters

namespace CylinderNonsqueezing
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE SmoothProfiles HamiltonianPeriodic
open ExteriorHamiltonian PushedBall CylinderParameters
variable {κ : Type} [Fintype κ] [DecidableEq κ]

 theorem radius_le_of_embedding (j₀ : κ) {L R M : ℝ} (hL : 0 < L) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (e : OpenPartialHomeomorph (Vector κ) (Vector κ))
    (he : ContDiffOn ℝ ∞ e e.source) (hs : e.source = domain L)
    (hω : ∀ z ∈ e.source, ComplexSymplectic.Preserves (fderiv ℝ e z))
    (hbounded : ∀ z ∈ e.target, ‖z‖^2 ≤ M)
    (hcylinder : ∀ z ∈ e.target, ‖z j₀‖^2 ≤ R) : L ≤ R := by
   by_contra hn
   have hRL : R < L := lt_of_not_ge hn
   obtain ⟨r,ε,hr,hrπ,hε,hεL,hm⟩ := exists_ball_parameters (mul_nonneg Real.pi_pos.le hR) hL
     (mul_lt_mul_of_pos_left hRL Real.pi_pos)
   let m := ballHeight r L ε
   have hεL' : ε ≤ L := by linarith
   have hRm : Real.pi*R < m := hm.trans_le (ballHeight_lower hr.le L hε hεL.le)
   obtain ⟨b,T,δ,hb,hbπ,hδ,hT,hmag,hcontain⟩ := exists_parameters j₀ hR hM hRm
   let d := weights j₀ (3*Real.pi/2) b
   obtain ⟨hdb,hdb0,hdD,hdπ,hgap⟩ := weights_bounds j₀ hb hbπ
   have hQ (z : Vector κ) (hz : z ∈ e.target) : energy d z < T :=
     hcontain z (hbounded z hz) (hcylinder z hz)
   have hD (z) (hz : z ∈ e.source) := ComplexSymplectic.invertible (hω z hz)
   let H₀ := pushed e r L ε
   have hH₀ : ContDiff ℝ ∞ H₀ := contDiff_pushed e he hs hD hε hεL'
   have hH₀0 (z : Vector κ) : 0 ≤ H₀ z := (pushed_bounds e hr.le hε z).1
   have hH₀m (z : Vector κ) : H₀ z ≤ m := (pushed_bounds e hr.le hε z).2
   have hS : IsCompact (e '' core L ε) := (core_compact L ε).image_of_continuousOn
     (e.continuousOn.mono (by rw [hs]; exact core_subset_domain hε hεL'))
   obtain ⟨B,hB,hrem⟩ := bounded_remainder hH₀ hH₀m hS
     (fun z hz => pushed_plateau e hε hεL' hz) d hb hdb hδ (by linarith : 0 ≤ T+δ)
   have h0 : (0 : Vector κ) ∈ e.source := by rw [hs]; exact zero_mem_domain hL
   have hflat := full_flat d hδ (pushed_flat e (r := r) hs hε hεL') (hQ _ (e.map_source h0))
   have hnonneg (z : Vector κ) : 0 ≤ full H₀ d T δ z := add_nonneg (hH₀0 z) (potential_nonneg d T hδ z)
   obtain ⟨x,hp,ha,hx⟩ := exists_positive_at_flat_point j₀ (contDiff_full hH₀ d T δ) hnonneg (e 0)
     hflat d (div_pos hb (by norm_num : (0:ℝ) < 2)) hb hB
     (by positivity : 0 ≤ 3*Real.pi/2)
     (fun j => by dsimp [d]; linarith [hdb j])
     (by dsimp [d]; linarith) hdD hgap hrem
   have hn := all_orbits_nonpos j₀ hH₀ hH₀m hH₀0 d (fun j => hb.le.trans (hdb j))
     (by dsimp [d,weights]; simp only [ite_true]; linarith [Real.pi_pos]) hdπ
     (by dsimp [d,weights]; simp only [ite_true]; linarith [Real.pi_pos]) hδ
     (by simpa only [d,weights,ite_true] using hmag)
     (fun z hz => (hQ z hz).le)
     (fun z hz => pushed_plateau_outside e hs hε hεL' hz)
     (fun x hxt hp hx t => pushed_full_slow e he hω hs hr.le hrπ hε hεL' d hδ
       (fun z hz => (hQ z hz).le) hxt hp hx t) hx hp
   exact (not_lt_of_ge hn) ha

end
end CylinderNonsqueezing
end NonsqueezingInline

end OAI
