import OAI.Analysis.AncientFlat.Profile.RadialHolderOn
import OAI.Analysis.AncientFlat.Regularity.HolderProducts

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff
namespace ParabolicCore
open ParabolicInterior ParabolicAnnular
variable {V : Type} [NormedAddCommGroup V]
def outer : Set (V × ℝ) := {p | ‖p.1‖<4 ∧ -257<p.2 ∧ p.2≤-1/2}
def inner : Set (V × ℝ) := {p | ‖p.1‖<2 ∧ -(33/2)<p.2 ∧ p.2≤-1/2}
def rectangle : Set (ℝ × ℝ) := Icc 0 4 ×ˢ Icc (1/2) 257
def argument (z : ℝ × ℝ) : ℝ := z.1^2/Real.sqrt z.2
def principal (G : ℝ → ℝ) (z : ℝ × ℝ) : ℝ := G (argument z)^2/16
def potential (G : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  -z.2⁻¹*(argument z*derivWithin G (Ici 0) (argument z)/G (argument z))
lemma argument_nonneg {z : ℝ × ℝ} (_hz : z∈rectangle) : 0≤argument z := by unfold argument; positivity
lemma argument_smooth : ContDiffOn ℝ ∞ argument rectangle := by
  apply (contDiff_fst.contDiffOn.pow 2).div
    (contDiff_snd.contDiffOn.sqrt (fun z hz => ne_of_gt (by linarith [hz.2.1] : 0<z.2)))
  intro z hz
  exact (Real.sqrt_pos.mpr (by linarith [hz.2.1] : 0<z.2)).ne'
lemma coeff_smooth (G : ℝ → ℝ) (κ : ℝ) (hκ : 0<κ)
    (hG : ContDiffOn ℝ ∞ G (Ici 0)) (hpos : ∀ y : ℝ, 0≤y → κ≤G y) :
    ContDiffOn ℝ 1 (principal G) rectangle ∧ ContDiffOn ℝ 1 (potential G) rectangle := by
  have harg : ContDiffOn ℝ 1 argument rectangle := argument_smooth.of_le (by simp)
  have hGV : ContDiffOn ℝ 1 (fun z => G (argument z)) rectangle :=
    (hG.of_le (show (1:ℕ∞ω)≤∞ by simp)).comp harg (fun _ hz => argument_nonneg hz)
  have hGD : ContDiffOn ℝ 1 (derivWithin G (Ici 0)) (Ici 0) :=
    hG.derivWithin (uniqueDiffOn_Ici 0) (by
      norm_num only [one_add_one_eq_two]
      exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  refine ⟨hGV.pow 2 |>.div contDiffOn_const (by norm_num),?_⟩
  have hT : ContDiffOn ℝ 1 (fun z : ℝ × ℝ => z.2) rectangle := contDiff_snd.contDiffOn
  have hi : ContDiffOn ℝ 1 (fun z : ℝ × ℝ => -z.2⁻¹) rectangle :=
    (hT.inv (fun z hz => ne_of_gt (by linarith [hz.2.1] : 0<z.2))).neg
  exact hi.mul ((harg.mul (hGD.comp harg (fun _ hz => argument_nonneg hz))).div hGV
    (fun z hz => (hκ.trans_le (hpos _ (argument_nonneg hz))).ne'))
lemma potential_eq (G : ℝ → ℝ) (p : V × ℝ) :
    potential G (‖p.1‖,-p.2)=profilePotential G p := by
  unfold potential profilePotential argument
  by_cases hy : ‖p.1‖^2/Real.sqrt (-p.2)=0
  · simp only [hy,zero_mul,zero_div,mul_zero]
  · have hpos : 0<‖p.1‖^2/Real.sqrt (-p.2) := lt_of_le_of_ne (by positivity) (Ne.symm hy)
    rw [derivWithin_of_mem_nhds (Ici_mem_nhds hpos)]
lemma profile_core_holder (G : ℝ → ℝ) (κ α : ℝ) (hκ : 0<κ) (hα : 0<α) (hα1 : α<1)
    (hG : ContDiffOn ℝ ∞ G (Ici 0)) (hpos : ∀ y : ℝ, 0≤y → κ≤G y) :
    ∃ K : ℝ, 0<K ∧ HolderBound α outer (profilePrincipal (V := V) G) K ∧
      HolderBound α outer (fun p : V × ℝ => (profilePotential G p : ℂ)) K ∧
      ∀ p : V × ℝ, p∈outer → κ^2/16≤profilePrincipal G p := by
  have hk : IsCompact rectangle := isCompact_Icc.prod isCompact_Icc
  have hkc : Convex ℝ rectangle := (convex_Icc _ _).prod (convex_Icc _ _)
  have hm : ∀ p∈(outer : Set (V × ℝ)), (‖p.1‖,-p.2)∈rectangle := by
    intro p hp
    exact ⟨⟨norm_nonneg _,hp.1.le⟩,⟨by linarith [hp.2.2],by linarith [hp.2.1]⟩⟩
  obtain ⟨K1,hK1,ha⟩ := compact_radial_holder_on α hα hα1.le (principal G) rectangle hk hkc
    (coeff_smooth G κ hκ hG hpos).1 outer hm
  obtain ⟨K2,hK2,hb⟩ := compact_radial_holder_on α hα hα1.le (potential G) rectangle hk hkc
    (coeff_smooth G κ hκ hG hpos).2 outer hm
  have ha' : HolderBound α outer (profilePrincipal (V := V) G) K1 := ha
  have hb' : HolderBound α outer (fun p : V × ℝ => (profilePotential G p : ℂ)) K2 := by
    constructor
    · intro p hp
      simpa only [←potential_eq G p,Complex.norm_real] using hb.1 p hp
    · intro p hp q hq
      simpa only [←potential_eq G p,←potential_eq G q,←Complex.ofReal_sub,Complex.norm_real] using hb.2 p hp q hq
  refine ⟨K1+K2,by positivity,ha'.mono (by linarith),hb'.mono (by linarith),?_⟩
  intro p hp
  have hGp := hpos (‖p.1‖^2/Real.sqrt (-p.2)) (by positivity)
  dsimp [profilePrincipal]
  exact div_le_div_of_nonneg_right ((sq_le_sq₀ hκ.le (hκ.le.trans hGp)).mpr hGp) (by norm_num)
end ParabolicCore

end

end OAI
