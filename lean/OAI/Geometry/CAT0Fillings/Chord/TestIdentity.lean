import Mathlib
import OAI.Geometry.CAT0Fillings.Chord.Profile
import OAI.Geometry.CAT0Fillings.Chord.GroundProducts

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.Conformal
noncomputable def profileGradient {E : Type*} [AddCommGroup E] [Module ℝ E]
    (m : ℕ) (α β κ : ℝ) (f : ℝ → ℝ) (r u : ℝ) (R V : E) : E :=
  if 0 < u then profileRD m α β κ f r u • R+profileZD m α β κ f r u • V else 0
lemma radial_profile_complete {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R V : E) {n β κ r u : ℝ} (f : ℝ → ℝ) (hu : 0 ≤ u) (hb : 0 < β)
    (hn : n*β = 1+2*β) :
    κ^2*(n*(u^(2+2*β)*f (κ*r*u^β))*‖R‖^2+
      r*inner ℝ R (profileGradient 0 (2+2*β) β κ f r u R V)+
      β*inner ℝ V (profileGradient 2 (1+2*β) β κ f r u R V)) =
      (n*f (κ*r*u^β)+(κ*r*u^β)*deriv f (κ*r*u^β))*
        ‖(κ*u^(1+β)) • R+(κ*β*r*u^β) • V‖^2 := by
  rcases hu.eq_or_lt with hu|hu
  · subst u
    simp [profileGradient,Real.zero_rpow hb.ne',Real.zero_rpow (by linarith : 1+β ≠ 0),
      Real.zero_rpow (by linarith : 2+2*β ≠ 0)]
  · simp only [profileGradient,ite_eq_left hu]
    exact radial_profile_algebra R V f hu hn
end CAT0Fillings.Conformal
namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma closed_added_tests (hz : IsCycle T) (o : X) (v : q.Sobolev) {κ β B : ℝ}
    {f : ℝ → ℝ} (hb : 0 < β) (hB : 0 ≤ B) (hf : ContDiff ℝ 1 f)
    (hfB : ∀ t, |f t| ≤ B ∧ |deriv f t| ≤ B)
    (hv : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion v x)
    (hm : ∀ b : ℝ, 0 < b → MemLp (q.inclusion v) (ENNReal.ofReal b) (MassMeasure.currentMassMeasure hT))
    (hpow : ∀ γ : ℝ, 1 ≤ γ → ∃ L : q.Sobolev,
      (q.closedGradient L : _ → _) =ᵐ[q.atlasMeasure]
        (fun z => (γ*(q.inclusion v (q.atlasParam z))^(γ-1)) • q.closedGradient v z)) :
    ∃ G Q : q.Sobolev,
      (q.inclusion G : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => (q.inclusion v x)^(2+2*β)*f (κ*dist o x*(q.inclusion v x)^β)) ∧
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => dist o x^2*(q.inclusion v x)^(1+2*β)*f (κ*dist o x*(q.inclusion v x)^β)) ∧
      (q.closedGradient G : _ → _) =ᵐ[q.atlasMeasure]
        (fun z => Conformal.profileGradient 0 (2+2*β) β κ f (dist o (q.atlasParam z))
          (q.inclusion v (q.atlasParam z)) (q.gradient (LipschitzWith.dist_right o) z) (q.closedGradient v z)) ∧
      (q.closedGradient Q : _ → _) =ᵐ[q.atlasMeasure]
        (fun z => Conformal.profileGradient 2 (1+2*β) β κ f (dist o (q.atlasParam z))
          (q.inclusion v (q.atlasParam z)) (q.gradient (LipschitzWith.dist_right o) z) (q.closedGradient v z)) := by
  have hr (x : X) : 0 ≤ dist o x ∧ dist o x ≤ Metric.diam (univ : Set X) :=
    ⟨dist_nonneg,Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ o) (mem_univ x)⟩
  obtain ⟨G,hG,hDG⟩ := q.closed_conformal hz (LipschitzWith.dist_right o) hr
    (m := 0) (α := 2+2*β) (κ := κ) (by linarith) hb hB hf hfB v hv hm hpow
  obtain ⟨Q,hQ,hDQ⟩ := q.closed_conformal hz (LipschitzWith.dist_right o) hr
    (m := 2) (α := 1+2*β) (κ := κ) (by linarith) hb hB hf hfB v hv hm hpow
  refine ⟨G,Q,?_,?_,hDG,hDQ⟩
  · simpa only [Conformal.profile,pow_zero,one_mul] using hG
  · exact hQ
end CAT0Fillings.ChartGeometry
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.Conformal
lemma radial_value_cancel {u β r f : ℝ} (hu : 0 ≤ u) (hb : 0 < β) :
    u*(r^2*u^(1+2*β)*f) = r^2*(u^(2+2*β)*f) := by
  have he : u*u^(1+2*β) = u^(2+2*β) := by
    conv_lhs => lhs; rw [←Real.rpow_one u]
    rw [←Real.rpow_add' hu (by linarith : 1+(1+2*β) ≠ 0)]
    congr 1
    ring
  calc
    _ = r^2*(u*u^(1+2*β))*f := by ring
    _ = _ := by rw [he]; ring
lemma completed_profile_cancel {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R V : E) {n β κ r u : ℝ} (f : ℝ → ℝ) (hu : 0 ≤ u) (hb : 0 < β)
    (hn : n*β = 1+2*β) :
    (n*f (κ*r*u^β)+(κ*r*u^β)*deriv f (κ*r*u^β))*
        ‖(κ*u^(1+β)) • R+(κ*β*r*u^β) • V‖^2 =
    κ^2*((n*‖R‖^2-n/4*r^2)*(u^(2+2*β)*f (κ*r*u^β))+
      r*inner ℝ R (profileGradient 0 (2+2*β) β κ f r u R V)+
      β*inner ℝ V (profileGradient 2 (1+2*β) β κ f r u R V)+
      n/4*(u*(r^2*u^(1+2*β)*f (κ*r*u^β)))) := by
  rw [←radial_profile_complete R V f hu hb hn,radial_value_cancel hu hb]
  ring
end CAT0Fillings.Conformal
namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)
lemma added_tests_identity (o : X) (v G Q : q.Sobolev) {κ β : ℝ} {f : ℝ → ℝ}
    (hb : 0 < β) (hn : (k+1:ℝ)*β = 1+2*β)
    (hv : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion v x)
    (hG : (q.inclusion G : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
      (fun x => (q.inclusion v x)^(2+2*β)*f (κ*dist o x*(q.inclusion v x)^β)))
    (hQ : (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
      (fun x => dist o x^2*(q.inclusion v x)^(1+2*β)*f (κ*dist o x*(q.inclusion v x)^β)))
    (hDG : (q.closedGradient G : _ → _) =ᵐ[q.atlasMeasure]
      (fun z => Conformal.profileGradient 0 (2+2*β) β κ f (dist o (q.atlasParam z))
        (q.inclusion v (q.atlasParam z)) (q.gradient (LipschitzWith.dist_right o) z) (q.closedGradient v z)))
    (hDQ : (q.closedGradient Q : _ → _) =ᵐ[q.atlasMeasure]
      (fun z => Conformal.profileGradient 2 (1+2*β) β κ f (dist o (q.atlasParam z))
        (q.inclusion v (q.atlasParam z)) (q.gradient (LipschitzWith.dist_right o) z) (q.closedGradient v z))) :
    (fun z => ((k+1:ℝ)*f (κ*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β)+
      (κ*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β)*
        deriv f (κ*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β))*‖q.chordXi o v κ β z‖^2)
      =ᵐ[q.atlasMeasure] (fun z => κ^2*(((k+1:ℝ)*‖q.gradient (LipschitzWith.dist_right o) z‖^2-
        (k+1:ℝ)/4*dist o (q.atlasParam z)^2)*q.inclusion G (q.atlasParam z)+
        dist o (q.atlasParam z)*inner ℝ (q.gradient (LipschitzWith.dist_right o) z) (q.closedGradient G z)+
        β*inner ℝ (q.closedGradient v z) (q.closedGradient Q z)+
        (k+1:ℝ)/4*(q.inclusion v (q.atlasParam z)*q.inclusion Q (q.atlasParam z)))) := by
  filter_upwards [hDG,hDQ,q.atlas_preserving.quasiMeasurePreserving.ae hv,
    q.atlas_preserving.quasiMeasurePreserving.ae hG,q.atlas_preserving.quasiMeasurePreserving.ae hQ]
    with z hDG hDQ hv hG hQ
  rw [hDG,hDQ,hG,hQ]
  exact Conformal.completed_profile_cancel (q.gradient (LipschitzWith.dist_right o) z)
    (q.closedGradient v z) f hv hb hn
end CAT0Fillings.ChartGeometry
end

end OAI
