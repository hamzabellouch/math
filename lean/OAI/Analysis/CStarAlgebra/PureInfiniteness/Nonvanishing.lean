import OAI.Analysis.CStarAlgebra.PureInfiniteness.Graph

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
universe u v
variable {A : Type u} [CStarAlgebra A]
local instance nonvanishingPartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance nonvanishingStarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance nonvanishingOperatorPartialOrder (J : Type*)
    [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J] :
    PartialOrder (J →L[ℂ] J) := CStarAlgebra.spectralOrder _
local instance nonvanishingOperatorStarOrderedRing (J : Type*)
    [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J] :
    StarOrderedRing (J →L[ℂ] J) := CStarAlgebra.spectralOrderedRing _
lemma cut_eq_zero_of_norm_le {a : A} (ha : 0 ≤ a) {l : ℝ} (hl : ‖a‖ ≤ l) :
    cut a l = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  change ‖cfcₙ (fun t : ℝ => max (t-l) 0) a‖ ≤ 0
  apply norm_cfcₙ_le
  intro r hr
  have hb := NonUnitalIsometricContinuousFunctionalCalculus.norm_quasispectrum_le a hr
    ha.isSelfAdjoint
  have hb' : |r| ≤ ‖a‖ := by simpa only [Real.norm_eq_abs] using hb
  have ht : r ≤ l := (le_abs_self r).trans (hb'.trans hl)
  rw [max_eq_right (sub_nonpos.mpr ht), norm_zero]

theorem quantitative_nonvanishing {d y : A} (hy : 0 ≤ y)
    (h : ∀ R : HilbertRep.{u,u} A, R.hom d=0 → ‖R.hom y‖ ≤ (1/4 : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ R : HilbertRep.{u,u} A,
      (3/8 : ℝ) < ‖R.hom y‖ → δ < ‖R.hom d‖ := by
  classical
  by_contra! hh
  let η : ℕ → ℝ := fun n => 1 / ((n : ℝ)+2)
  have hηpos (n : ℕ) : 0 < η n := by dsimp [η]; positivity
  have hηlt (n : ℕ) : η n < 1 := by
    dsimp [η]
    apply (div_lt_one (by positivity)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hbad (n : ℕ) : ∃ R : HilbertRep.{u,u} A,
      (3/8 : ℝ) < ‖R.hom y‖ ∧ ‖R.hom d‖ ≤ η n := hh (η n) (hηpos n) (hηlt n)
  choose R hRy hRd using hbad
  let π := fun n => (R n).hom
  let a := cut y (5/16)
  have ha : ∀ n, (1/16 : ℝ) < ‖π n a‖ := by
    intro n
    have h₁ : ‖π n y - π n a‖ ≤ (5/16 : ℝ) := by
      rw [← map_sub]
      exact (NonUnitalStarAlgHom.norm_apply_le (π n) _).trans
        (norm_sub_cut_le hy (by norm_num))
    have h₂ := norm_sub_norm_le (π n y) (π n a)
    have h₃ := hRy n
    change (3/8 : ℝ) < ‖π n y‖ at h₃
    linarith
  choose ξ hξ hξa using fun n => (π n a).exists_lt_apply_of_lt_opNorm (ha n)
  have hnξ : ∀ n, ‖ξ n‖ ≤ 1 := fun n => (hξ n).le
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  have hω : (ω : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  have hη : Tendsto η (ω : Filter ℕ) (𝓝 0) := by
    have he : η = fun n : ℕ => 1 / (((n+1 : ℕ) : ℝ)+1) := by
      funext n
      dsimp [η]
      push_cast
      congr 1; ring
    rw [he]
    exact ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)).mono_left hω
  let ρ : HilbertRep.{u,u} A := ⟨LimitHilbert ω π ξ hnξ, limitRep ω π ξ hnξ⟩
  have hd₀ : ρ.hom d=0 := limitRep_annihilates ω π ξ hnξ d
    (squeeze_zero (fun n => norm_nonneg _) hRd hη)
  have han : ρ.hom a ≠ 0 := limitRep_nonzero ω π ξ hnξ a (by norm_num : (0:ℝ)<1/16)
    (Filter.Eventually.of_forall (fun n => (hξa n).le))
  apply han
  change ρ.hom (cut y (5/16))=0
  rw [map_cut_sa ρ.hom hy.isSelfAdjoint (by norm_num)]
  exact cut_eq_zero_of_norm_le (map_nonneg ρ.hom hy) ((h ρ hd₀).trans (by norm_num))

theorem quantitative_nonvanishing_general {d y : A} (hy : 0 ≤ y)
    {s s' : ℝ} (hs : 0 ≤ s) (hss : s < s')
    (h : ∀ R : HilbertRep.{u,u} A, R.hom d=0 → ‖R.hom y‖ ≤ s) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ R : HilbertRep.{u,u} A,
      s' < ‖R.hom y‖ → δ < ‖R.hom d‖ := by
  classical
  by_contra! hh
  let η : ℕ → ℝ := fun n => 1 / ((n : ℝ)+2)
  have hηpos (n : ℕ) : 0 < η n := by dsimp [η]; positivity
  have hηlt (n : ℕ) : η n < 1 := by
    dsimp [η]
    apply (div_lt_one (by positivity)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hbad (n : ℕ) : ∃ R : HilbertRep.{u,u} A,
      s' < ‖R.hom y‖ ∧ ‖R.hom d‖ ≤ η n := hh (η n) (hηpos n) (hηlt n)
  choose R hRy hRd using hbad
  let π := fun n => (R n).hom
  let a := cut y ((s+s')/2)
  have ha : ∀ n, ((s'-s)/2) < ‖π n a‖ := by
    intro n
    have h₁ : ‖π n y - π n a‖ ≤ ((s+s')/2) := by
      rw [← map_sub]
      exact (NonUnitalStarAlgHom.norm_apply_le (π n) _).trans
        (norm_sub_cut_le hy (by linarith))
    have h₂ := norm_sub_norm_le (π n y) (π n a)
    have h₃ := hRy n
    change s' < ‖π n y‖ at h₃
    linarith
  choose ξ hξ hξa using fun n => (π n a).exists_lt_apply_of_lt_opNorm (ha n)
  have hnξ : ∀ n, ‖ξ n‖ ≤ 1 := fun n => (hξ n).le
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  have hω : (ω : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  have hη : Tendsto η (ω : Filter ℕ) (𝓝 0) := by
    have he : η = fun n : ℕ => 1 / (((n+1 : ℕ) : ℝ)+1) := by
      funext n
      dsimp [η]
      push_cast
      congr 1; ring
    rw [he]
    exact ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)).mono_left hω
  let ρ : HilbertRep.{u,u} A := ⟨LimitHilbert ω π ξ hnξ, limitRep ω π ξ hnξ⟩
  have hd₀ : ρ.hom d=0 := limitRep_annihilates ω π ξ hnξ d
    (squeeze_zero (fun n => norm_nonneg _) hRd hη)
  have han : ρ.hom a ≠ 0 := limitRep_nonzero ω π ξ hnξ a (by linarith : (0:ℝ)<(s'-s)/2)
    (Filter.Eventually.of_forall (fun n => (hξa n).le))
  apply han
  change ρ.hom (cut y ((s+s')/2))=0
  rw [map_cut_sa ρ.hom hy.isSelfAdjoint (by linarith)]
  exact cut_eq_zero_of_norm_le (map_nonneg ρ.hom hy) ((h ρ hd₀).trans (by linarith))

end MainGap

end

end OAI
