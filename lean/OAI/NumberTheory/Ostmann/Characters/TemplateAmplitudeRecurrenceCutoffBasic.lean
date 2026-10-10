import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceFrequencySupport

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template

theorem reversal_frequency_abs_le {P : ℕ+} {s v w HL HR U : ℤ}
    {Vmax Hmax Pmin : ℝ} (he : v*HR-w*HL=s*(P:ℤ))
    (hv : |(v:ℝ)|≤Vmax) (hw : |(w:ℝ)|≤Vmax)
    (hL : |(HL:ℝ)|≤Hmax) (hR : |(HR:ℝ)|≤Hmax)
    (hPmin : 0<Pmin) (hP : Pmin≤(P:ℝ))
    (hcap : 2*Vmax*Hmax≤(U:ℝ)*Pmin) : |s|≤U := by
  have hV0 : 0≤Vmax := (abs_nonneg _).trans hv
  have hH0 : 0≤Hmax := (abs_nonneg _).trans hL
  have hU0 : 0≤(U:ℝ) := by
    by_contra hn
    have hn' : (U:ℝ)*Pmin<0 := mul_neg_of_neg_of_pos (lt_of_not_ge hn) hPmin
    nlinarith [mul_nonneg hV0 hH0]
  have hPr : 0<(P:ℝ) := hPmin.trans_le hP
  have her : (v:ℝ)*HR-(w:ℝ)*HL=(s:ℝ)*P := by exact_mod_cast he
  have hbound : |(s:ℝ)| * (P:ℝ)≤2*Vmax*Hmax := by
    calc
      _ = |(v:ℝ)*HR-(w:ℝ)*HL| := by rw [her,abs_mul,abs_of_pos hPr]
      _ ≤ |(v:ℝ)*HR|+|(w:ℝ)*HL| := abs_sub _ _
      _ = |(v:ℝ)| * |(HR:ℝ)|+|(w:ℝ)| * |(HL:ℝ)| := by rw [abs_mul,abs_mul]
      _ ≤ Vmax*Hmax+Vmax*Hmax := add_le_add
        (mul_le_mul hv hR (abs_nonneg _) hV0) (mul_le_mul hw hL (abs_nonneg _) hV0)
      _ = 2*Vmax*Hmax := by ring
  have hfinal : |(s:ℝ)|≤(U:ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hP hU0
    nlinarith
  exact_mod_cast hfinal

theorem reversal_frequency_mem_erase_Icc {P : ℕ+} {s v w HL HR U : ℤ}
    {Vmax Hmax Pmin : ℝ} (hN : v*HR-w*HL≠0) (he : v*HR-w*HL=s*(P:ℤ))
    (hv : |(v:ℝ)|≤Vmax) (hw : |(w:ℝ)|≤Vmax)
    (hL : |(HL:ℝ)|≤Hmax) (hR : |(HR:ℝ)|≤Hmax)
    (hPmin : 0<Pmin) (hP : Pmin≤(P:ℝ))
    (hcap : 2*Vmax*Hmax≤(U:ℝ)*Pmin) : s∈(Finset.Icc (-U) U).erase 0 := by
  have hs : s≠0 := by intro hz; apply hN; simpa only [hz,zero_mul] using he
  exact Finset.mem_erase.mpr ⟨hs,Finset.mem_Icc.mpr
    (abs_le.mp (reversal_frequency_abs_le he hv hw hL hR hPmin hP hcap))⟩

end Ostmann.Characters.Template

end

end OAI
