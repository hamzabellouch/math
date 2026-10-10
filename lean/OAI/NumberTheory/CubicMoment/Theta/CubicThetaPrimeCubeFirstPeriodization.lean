import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeUnitMean
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalDilation

namespace OAI

/-! The first character branch as an actual periodic finite sum. The
coefficient is extended by zero on nonunits before additive reindexing. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaPrimeCubeFirstTerm (p : Eisenstein) (f : ℂ → ℂ) (b : Eisenstein) (z : ℂ) : ℂ :=
  cubicSymbol p (3*b)*f (z/(p:ℂ)+3*(b:ℂ)/(p:ℂ)^2)

def cubicThetaPrimeCubeFirstPeriodization (p : Eisenstein) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑' r : Residues (p^2),cubicThetaPrimeCubeFirstTerm p f (residueRepresentative (p^2) r) z

lemma cubicThetaPrimeCubeFirstTerm_congr {p : Eisenstein} (hp : primaryPrime p)
    (f : ℂ → ℂ) (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z)
    {b c : Eisenstein} (hbc : p^2∣b-c) (z : ℂ) :
    cubicThetaPrimeCubeFirstTerm p f b z=cubicThetaPrimeCubeFirstTerm p f c z := by
  have hpC : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  have hch : cubicSymbol p (3*b)=cubicSymbol p (3*c) := by
    apply cubicSymbol_congr
    apply residue_eq_of_dvd_sub
    rw [←mul_sub]
    exact dvd_mul_of_dvd_right ((dvd_pow_self p (by decide : (2:ℕ)≠0)).trans hbc) 3
  obtain ⟨m,hm⟩ := hbc
  have hb : b=c+p^2*m := by linear_combination hm
  have hx : z/(p:ℂ)+3*(b:ℂ)/(p:ℂ)^2=
      (z/(p:ℂ)+3*(c:ℂ)/(p:ℂ)^2)+3*(m:ℂ) := by
    rw [hb]
    push_cast
    field_simp [hpC]
    ring
  unfold cubicThetaPrimeCubeFirstTerm
  rw [hch,hx,hf]

lemma cubicThetaPrimeCubeFirstTerm_shift {p : Eisenstein} (hp : primaryPrime p)
    (f : ℂ → ℂ) (b w : Eisenstein) (z : ℂ) :
    cubicThetaPrimeCubeFirstTerm p f b (z+3*(w:ℂ))=
      cubicThetaPrimeCubeFirstTerm p f (b+p*w) z := by
  have hpC : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  have hch : cubicSymbol p (3*(b+p*w))=cubicSymbol p (3*b) := by
    apply cubicSymbol_congr
    apply residue_eq_of_dvd_sub
    refine ⟨3*w,?_⟩
    ring
  have hx : (z+3*(w:ℂ))/(p:ℂ)+3*(b:ℂ)/(p:ℂ)^2=
      z/(p:ℂ)+3*((b+p*w:Eisenstein):ℂ)/(p:ℂ)^2 := by
    push_cast
    field_simp [hpC]
    ring
  unfold cubicThetaPrimeCubeFirstTerm
  rw [hch,hx]

lemma cubicThetaPrimeCubeFirstPeriodization_periodic {p : Eisenstein} (hp : primaryPrime p)
    (f : ℂ → ℂ) (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z)
    (w : Eisenstein) (z : ℂ) :
    cubicThetaPrimeCubeFirstPeriodization p f (z+3*(w:ℂ))=
      cubicThetaPrimeCubeFirstPeriodization p f z := by
  let e : Residues (p^2) ≃ Residues (p^2) := Equiv.addRight (Ideal.Quotient.mk (modulus (p^2)) (p*w))
  unfold cubicThetaPrimeCubeFirstPeriodization
  calc
    _ = ∑' r : Residues (p^2),cubicThetaPrimeCubeFirstTerm p f
        (residueRepresentative (p^2) (e r)) z := by
      apply tsum_congr
      intro r
      rw [cubicThetaPrimeCubeFirstTerm_shift hp]
      apply cubicThetaPrimeCubeFirstTerm_congr hp f hf
      apply Ideal.mem_span_singleton.mp
      apply Ideal.Quotient.eq.mp
      change Ideal.Quotient.mk (modulus (p^2))
        (residueRepresentative (p^2) r+p*w)=
        Ideal.Quotient.mk (modulus (p^2)) (residueRepresentative (p^2) (e r))
      rw [residueRepresentative_spec,map_add,residueRepresentative_spec]
      rfl
    _ = _ := e.tsum_eq (fun r : Residues (p^2) =>
      cubicThetaPrimeCubeFirstTerm p f (residueRepresentative (p^2) r) z)

lemma cubicThetaPrimeCubeFirstPeriodization_continuous {p : Eisenstein} (hp : primaryPrime p)
    (f : C(ℂ,ℂ)) : Continuous (cubicThetaPrimeCubeFirstPeriodization p f) := by
  let : Finite (Residues (p^2)) := finite_residues (pow_ne_zero _ hp.2.ne_zero)
  let : Fintype (Residues (p^2)) := Fintype.ofFinite _
  unfold cubicThetaPrimeCubeFirstPeriodization
  simp_rw [tsum_fintype]
  apply continuous_finsetSum
  intro r _
  unfold cubicThetaPrimeCubeFirstTerm
  fun_prop

end CubicFirstMoment

end

end OAI
