import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalDilation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalAffine

namespace OAI

/-! The horizontal periodization appearing in the bottom Hecke branch. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaHorizontalFraction (a : Eisenstein) (f : ℂ → ℂ) (b : Eisenstein) (z : ℂ) : ℂ :=
  f ((z+3*(b:ℂ))/(a:ℂ))

def cubicThetaHorizontalPeriodization (a : Eisenstein) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑' r : Residues a,cubicThetaHorizontalFraction a f (residueRepresentative a r) z

lemma cubicThetaHorizontalFraction_congr {a : Eisenstein} (ha : a≠0)
    (f : ℂ → ℂ) (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z)
    {b c : Eisenstein} (hbc : a∣b-c) (z : ℂ) :
    cubicThetaHorizontalFraction a f b z=cubicThetaHorizontalFraction a f c z := by
  have haC : (a:ℂ)≠0 := fun he => ha (Subtype.ext he)
  obtain ⟨m,hm⟩ := hbc
  have hb : b=c+a*m := by linear_combination hm
  have hx : (z+3*(b:ℂ))/(a:ℂ)=(z+3*(c:ℂ))/(a:ℂ)+3*(m:ℂ) := by
    rw [hb]
    push_cast
    field_simp [haC]
    ring
  unfold cubicThetaHorizontalFraction
  rw [hx,hf]

lemma cubicThetaHorizontalPeriodization_periodic {a : Eisenstein} (ha : a≠0)
    (f : ℂ → ℂ) (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z)
    (w : Eisenstein) (z : ℂ) :
    cubicThetaHorizontalPeriodization a f (z+3*(w:ℂ))=cubicThetaHorizontalPeriodization a f z := by
  let e : Residues a ≃ Residues a := Equiv.addRight (Ideal.Quotient.mk (modulus a) w)
  unfold cubicThetaHorizontalPeriodization
  calc
    _ = ∑' r : Residues a,cubicThetaHorizontalFraction a f
        (residueRepresentative a (e r)) z := by
      apply tsum_congr
      intro r
      have he : cubicThetaHorizontalFraction a f (residueRepresentative a r) (z+3*(w:ℂ))=
          cubicThetaHorizontalFraction a f (residueRepresentative a r+w) z := by
        unfold cubicThetaHorizontalFraction
        congr 2
        push_cast
        ring
      rw [he]
      apply cubicThetaHorizontalFraction_congr ha f hf
      apply Ideal.mem_span_singleton.mp
      apply Ideal.Quotient.eq.mp
      change Ideal.Quotient.mk (modulus a) (residueRepresentative a r+w)=
        Ideal.Quotient.mk (modulus a) (residueRepresentative a (e r))
      rw [residueRepresentative_spec,map_add,residueRepresentative_spec]
      rfl
    _ = _ := e.tsum_eq (fun r : Residues a => cubicThetaHorizontalFraction a f (residueRepresentative a r) z)

lemma cubicThetaHorizontalPeriodization_continuous {a : Eisenstein} (ha : a≠0)
    (f : C(ℂ,ℂ)) : Continuous (cubicThetaHorizontalPeriodization a f) := by
  let : Finite (Residues a) := finite_residues ha
  let : Fintype (Residues a) := Fintype.ofFinite _
  unfold cubicThetaHorizontalPeriodization
  simp_rw [tsum_fintype]
  apply continuous_finsetSum
  intro r _
  unfold cubicThetaHorizontalFraction
  fun_prop

lemma cubicThetaHorizontalPeriodization_integrable {a : Eisenstein} (ha : a≠0)
    (f : C(ℂ,ℂ)) : IntegrableOn (cubicThetaHorizontalPeriodization a f) cubicThetaHorizontalCell := by
  obtain ⟨K,hK,hsub⟩ := cubicThetaHorizontalCell_compact_container
  exact ((cubicThetaHorizontalPeriodization_continuous ha f).continuousOn.integrableOn_compact hK).mono_set hsub

end CubicFirstMoment

end

end OAI
