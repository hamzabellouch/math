import OAI.Analysis.FourierLLogL.Weak.Signed

noncomputable section
open MeasureTheory Filter Set Function
open scoped ENNReal BigOperators Topology

namespace OAI

namespace FourierLLogL.Weak
open Real
open scoped Classical

def renorm (f : Torus → ℂ) (b : ℝ) := fun x => ((b⁻¹:ℝ):ℂ)*f x

lemma young_renorm (f : Torus → ℂ) (b : ℝ) (hh : 0 < b) :
    Young (renorm f b)=fun x => priceΦ (‖f x‖/b) := by
  funext x; unfold Young renorm
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.2 hh),←div_eq_inv_mul]
lemma bill_renorm (f : Torus → ℂ) (b : ℝ) (hh : 0 < b) :
    modBill (renorm f b) 1= modBill f b := by
  rw [mod_unit,show (fun x => Young (renorm f b) x)=_ from young_renorm _ _ hh]; rfl
lemma lux_exists {f : Torus → ℂ} (h : MemLLogL f) : (luxSet f).Nonempty := by
  let T := modBill f 1; let b := max T 1
  have hb : 1 ≤ b := le_max_right _ _
  have hh : 0 < b := by linarith
  refine ⟨b, hh,?_⟩
  let g := renorm f b
  have HG : Integrable (Young g) law := (mem_dilate _ h).2
  rw [← bill_renorm f b hh,mod_unit]
  apply le_trans (b:=∫ x,b⁻¹*Young f x ∂law)
  · apply integral_mono HG ((show Integrable (Young f) law from h.2).const_mul _)
    rw [← show (fun x => Young (renorm f b) x)=Young g from rfl]
    intro x
    change Young (renorm f b) x ≤ _
    rw [young_renorm _ _ hh]
    let t := ‖f x‖
    have HT : 0 ≤ t := norm_nonneg _
    have hv : t/b ≤ t := div_le_self HT hb
    change (t/b)*log (2+t/b) ≤ b⁻¹*(t*log (2+t))
    rw [← mul_assoc,← div_eq_inv_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply log_le_log (by positivity); linarith
  · rw [integral_const_mul]
    rw [show (∫ x, Young f x ∂law) = T from (mod_unit f).symm,←div_eq_inv_mul]
    exact (div_le_one hh).mpr (le_max_left _ _)

lemma consequence_maximal (h : GoodBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Torus → ℂ), MemLLogL f →
      ∀ w : ℝ, 0 < w →
        w*circleMeasure.real (cloudSet f w) ≤ C*luxNorm f := by
  obtain ⟨C,hc,hF⟩ := circle_bill h
  refine ⟨C,hc,?_⟩
  intro f hf w hw
  let m := law.real (cloudSet f w)
  have H (b : ℝ) (hb : b∈luxSet f) :
      w*m ≤ C*b := by
    obtain ⟨hh,ht⟩ := hb
    let g := renorm f b
    have HE : inside g := ⟨mem_dilate _ hf,(bill_renorm f b hh).le.trans ht⟩
    have HP : cloudSet g (w/b)=cloudSet f w := by
      ext x
      rw [cloudy _ (by positivity) x,cloudy _ hw.le x]
      have Hz (i : ℕ) : ‖symmetricPartialSum g i x‖=‖symmetricPartialSum f i x‖/b := by
        unfold g renorm
        rw [symmetricPartialSum_const_mul,norm_mul, Complex.norm_real,Real.norm_eq_abs,
          abs_of_pos (inv_pos.2 hh),← div_eq_inv_mul]
      simp_rw [Hz,div_lt_div_iff_of_pos_right hh]
    have HI := hF g HE (w/b) (div_pos hw hh)
    rw [HP,div_mul_eq_mul_div] at HI
    exact (div_le_iff₀ hh).1 HI
  have HV : w*m/C ≤ sInf (luxSet f) :=
    le_csInf (lux_exists hf) fun b hb => (div_le_iff₀ hc).mpr ((H b hb).trans (le_of_eq (mul_comm C b)))
  change w*m ≤ C*sInf (luxSet f)
  rw [mul_comm C]; exact (div_le_iff₀ hc).1 HV

end FourierLLogL.Weak

end OAI
