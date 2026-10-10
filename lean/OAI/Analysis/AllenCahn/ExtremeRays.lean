import OAI.Analysis.AllenCahn.CompactCone

namespace OAI

noncomputable section
namespace DeGiorgiCompactness
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open Filter Topology
open scoped ContDiff
open MeasureTheory

def jetSegmentMass {n : ℕ} (ξ : Space n) (w : ℝ → ℝ) (R : ℝ)
    (g : JetSpace n) : ℝ := ∫ t in -R..R, g [] (t • ξ)*w t

def jetDirectional {n : ℕ} (ξ : Space n) (g : JetSpace n) : ℝ :=
  coordinateDual n (fun i => g [i] 0) ξ

lemma jetDirectional_continuous {n : ℕ} (ξ : Space n) :
    Continuous (jetDirectional ξ : JetSpace n → ℝ) := by
  apply Continuous.clm_apply _ continuous_const
  exact (coordinateDual n).continuous.comp (continuous_pi (fun i =>
    (continuous_eval_const 0).comp (continuous_apply [i])))

lemma jetDirectional_add_smul {n : ℕ} (ξ : Space n) (g h : JetSpace n) (a b : ℝ) :
    jetDirectional ξ (a • g+b • h) = a*jetDirectional ξ g+b*jetDirectional ξ h := by
  change coordinateDual n (a • (fun i => g [i] 0)+b • (fun i => h [i] 0)) ξ = _
  rw [map_add, map_smul, map_smul]
  rfl

lemma jetSegmentMass_add_smul {n : ℕ} (ξ : Space n) {w : ℝ → ℝ}
    (hw : Continuous w) (R : ℝ) (g h : JetSpace n) (a b : ℝ) :
    jetSegmentMass ξ w R (a • g+b • h) =
      a*jetSegmentMass ξ w R g+b*jetSegmentMass ξ w R h := by
  unfold jetSegmentMass
  have hg : Continuous (fun t : ℝ => g [] (t • ξ)*w t) :=
    ((g []).continuous.comp (continuous_id.smul continuous_const)).mul hw
  have hh : Continuous (fun t : ℝ => h [] (t • ξ)*w t) :=
    ((h []).continuous.comp (continuous_id.smul continuous_const)).mul hw
  have he : (fun t : ℝ => (a • g+b • h) [] (t • ξ)*w t) =
      fun t => a*(g [] (t • ξ)*w t)+b*(h [] (t • ξ)*w t) := by
    funext t
    change (a*g [] (t • ξ)+b*h [] (t • ξ))*w t = _
    ring
  rw [he, intervalIntegral.integral_add ((hg.const_mul a).intervalIntegrable _ _)
    ((hh.const_mul b).intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]

lemma jetSegmentMass_continuous_compact {n : ℕ} {K : Set (JetSpace n)}
    (hK : IsCompact K) (ξ : Space n) {w : ℝ → ℝ} (hw : Continuous w)
    {R : ℝ} (hR : 0 ≤ R) : Continuous (fun g : K => jetSegmentMass ξ w R g.val) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hf : Continuous (fun z : K × ℝ => z.1.val [] (z.2 • ξ)*w z.2) := by
    have hbase : Continuous (fun z : K × ℝ => z.1.val []) :=
      (continuous_apply []).comp (continuous_subtype_val.comp continuous_fst)
    exact (continuous_eval.comp (hbase.prodMk (continuous_snd.smul continuous_const))).mul
      (hw.comp continuous_snd)
  have HH := continuous_parametric_integral_of_continuous
    (f := fun (g : K) (t : ℝ) => g.val [] (t • ξ)*w t) (μ := volume) hf
    (isCompact_Icc : IsCompact (Set.Icc (-R) R))
  have he : (fun g : K => jetSegmentMass ξ w R g.val) =
      fun g : K => ∫ t in Set.Icc (-R) R, g.val [] (t • ξ)*w t := by
    funext g
    rw [jetSegmentMass, intervalIntegral.integral_of_le (by linarith : -R ≤ R),
      integral_Icc_eq_integral_Ioc]
  rw [he]
  exact HH

lemma jetCone_window_of_extreme {n : ℕ} {P : Space n → ℝ}
    (hK : IsCompact (pdeJetCone P)) (ξ : Space n) {w : ℝ → ℝ} (hw : Continuous w)
    {R : ℝ} (hR : 0 ≤ R) (c s : ℝ)
    (hext : ∀ g ∈ (pdeJetCone P).extremePoints ℝ,
      s*jetDirectional ξ g ≤ c*jetSegmentMass ξ w R g) :
    ∀ g ∈ pdeJetCone P, s*jetDirectional ξ g ≤ c*jetSegmentMass ξ w R g := by
  let A : Set (JetSpace n) := {g | g ∈ pdeJetCone P ∧
    s*jetDirectional ξ g ≤ c*jetSegmentMass ξ w R g}
  have hAclosed : IsClosed A := by
    have hp : IsClosed {g : pdeJetCone P |
        s*jetDirectional ξ g.val ≤ c*jetSegmentMass ξ w R g.val} :=
      isClosed_le (continuous_const.mul ((jetDirectional_continuous ξ).comp continuous_subtype_val))
        (continuous_const.mul (jetSegmentMass_continuous_compact hK ξ hw hR))
    have HH := (pdeJetCone_closed P).isClosedMap_subtype_val _ hp
    have he : A = Subtype.val '' {g : pdeJetCone P |
        s*jetDirectional ξ g.val ≤ c*jetSegmentMass ξ w R g.val} := by
      ext g
      simp only [A, Set.mem_ofPred_eq, Set.mem_image]
      constructor
      · rintro ⟨hg,hh⟩; exact ⟨⟨g,hg⟩, hh, rfl⟩
      · rintro ⟨h,hh,rfl⟩; exact ⟨h.property,hh⟩
    rw [he]
    exact HH
  have hAconvex : Convex ℝ A := by
    intro g hg h hh a b ha hb hab
    refine ⟨pdeJetCone_convex P hg.1 hh.1 ha hb hab, ?_⟩
    rw [jetDirectional_add_smul, jetSegmentMass_add_smul ξ hw]
    nlinarith [mul_le_mul_of_nonneg_left hg.2 ha, mul_le_mul_of_nonneg_left hh.2 hb]
  have hh : closure (convexHull ℝ ((pdeJetCone P).extremePoints ℝ)) ⊆ A :=
    closure_minimal (convexHull_min (fun g hg => ⟨hg.1, hext g hg⟩) hAconvex) hAclosed
  rw [closure_convexHull_extremePoints hK (pdeJetCone_convex P)] at hh
  intro g hg
  exact (hh hg).2

end DeGiorgiCompactness
end

end OAI
