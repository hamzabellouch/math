import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.PhysicalAngularBound

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def transportConeCoefficient (i : Fin 3) (p : Phase) : ℝ :=
  ((coneRadius 0 p.1)^2)⁻¹*transportAngularCore (coneDirection 0 p.1) (velocity p.2) i

def coneLorentz (s : Solution) (t : ℝ) (x : Vec) (p : Phase) : Vec :=
  s.E (t-coneRadius 0 p.1,x+p.1)+cross (velocity p.2) (s.B (t-coneRadius 0 p.1,x+p.1))

lemma transportConeCoefficient_contDiffAt (i : Fin 3) {p : Phase} (hp : p.1≠0) :
    ContDiffAt ℝ 1 (transportConeCoefficient i) p := by
  have hz : (0:Vec)≠p.1 := hp.symm
  have hr := (contDiffAt_coneRadius (k:=1) hz).comp p contDiffAt_fst
  have hn := (contDiffAt_coneDirection (k:=1) hz).comp p contDiffAt_fst
  have hu : ContDiffAt ℝ 1 (fun z : Phase => velocity z.2) p :=
    contDiff_velocity.contDiffAt.comp p contDiffAt_snd
  have hA := contDiffAt_transportAngularCore hn hu (cone_denom_pos p.2 _ (coneDirection_norm hz)).ne'
  have hi := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.contDiffAt.comp p hA
  exact ((hr.pow 2).inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz)))).mul hi

lemma coneLorentz_contDiffAt {s : Solution}
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    {t : ℝ} (x : Vec) {p : Phase} (hp : p.1≠0) (ht : 0<t-coneRadius 0 p.1) :
    ContDiffAt ℝ 1 (coneLorentz s t x) p := by
  have hr := (contDiffAt_coneRadius (k:=1) hp.symm).comp p contDiffAt_fst
  have hu : ContDiffAt ℝ 1 (fun z : Phase => velocity z.2) p :=
    contDiff_velocity.contDiffAt.comp p contDiffAt_snd
  have ha : ContDiffAt ℝ 1 (fun z : Phase => (t-coneRadius 0 z.1,x+z.1)) p :=
    (contDiffAt_const.sub hr).prodMk (contDiffAt_const.add contDiffAt_fst)
  have he := (field_contDiffAt_positive hE ht (x+p.1)).comp p ha
  have hb := (field_contDiffAt_positive hB ht (x+p.1)).comp p ha
  exact he.add (contDiff_cross.contDiffAt.comp p (hu.prodMk hb))

lemma coneLorentz_vlasov_before {s : Solution} {H t : ℝ}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (heq : EquationsBefore s H)
    (htH : t≤H) (x : Vec) {z : Vec} (hz : z∈retardedSpaceDomain t 0) (v : Vec) :
    fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (1,velocity v,coneLorentz s t x (z,v))=0 := by
  have hr : 0<coneRadius 0 z := norm_pos_iff.mpr (sub_ne_zero.mpr hz.1)
  have hh := particle_spacetime_vlasov_before hf heq hz.2 (by linarith : t-coneRadius 0 z<H) (x+z) v
  rw [fderiv_particleBySpacetime (particle_differentiableAt_positive hf hz.2 (x+z) v)] at hh
  exact hh

lemma electric_transport_division_annulus {s : Solution} {H t ε R : ℝ}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) (heq : EquationsBefore s H)
    (htH : t≤H) (hε : 0<ε) (hεR : ε≤R) (hRt : R<t) (x e : Vec) (i : Fin 3) :
    (∫ z in ball (0:Vec) R \ ball (0:Vec) ε, ∫ v,
      transportConeCoefficient i (z,v)*fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)) =
      (∫ n : Sphere, R^2*dot n.1 (∫ v, s.f (t-R,x+R • n.1,v) •
        transportSpatialFlux v e i (R • n.1)) ∂sphereMeasure)-
      (∫ n : Sphere, ε^2*dot n.1 (∫ v, s.f (t-ε,x+ε • n.1,v) •
        transportSpatialFlux v e i (ε • n.1)) ∂sphereMeasure)-
      ∫ z in ball (0:Vec) R \ ball (0:Vec) ε, ∫ v, s.f (t-coneRadius 0 z,x+z,v)*
        (divergence (transportSpatialFlux v e i) z+
          divergence (fun w => transportConeCoefficient i (z,w) •
            (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) v) := by
  have hk : ContDiffOn ℝ 1 (transportConeCoefficient i) (retardedSpaceDomain t 0 ×ˢ univ) :=
    fun p hp => (transportConeCoefficient_contDiffAt i hp.1.1.symm).contDiffWithinAt
  have hK : ContDiffOn ℝ 1 (coneLorentz s t x) (retardedSpaceDomain t 0 ×ˢ univ) :=
    fun p hp => (coneLorentz_contDiffAt hE hB x hp.1.1.symm hp.1.2).contDiffWithinAt
  have hh := retarded_spatial_annulus (e:=e) hf hc hε hεR hRt hk hK
    (fun z hz v => coneLorentz_vlasov_before hf heq htH x hz v)
  unfold transportSpatialFlux transportConeCoefficient at *
  simpa only [smul_smul,smul_eq_mul,mul_assoc] using hh

end RVM
end

end OAI
