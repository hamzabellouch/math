import OAI.NumberTheory.DirichletL.Moments.SecondBlockSupport
import OAI.NumberTheory.DirichletL.Moments.SourceDyadicShell

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSourceBlockWindows
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondSectorColumns
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open CenteredMomentSourceDyadicShell CenteredMomentHeckeColumnWindow
local notation "O" => ActualEisensteinCubic.O

 theorem physicalBlock_column_witnesses (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (U:Finset (CommonIndex C D)) (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    ∃I:sectorPool C hC.1 S,∃J:sectorPool D hD.1 S,
      β (C*I)≠0 ∧ β (D*J)≠0 ∧
      dyadicWeight (n 2) (Ideal.absNorm (I:Ideal O):ℝ)≠0 ∧
      dyadicWeight (n 3) (Ideal.absNorm (J:Ideal O):ℝ)≠0 := by
  unfold physicalBlock at hne
  obtain ⟨z,hzr,hz⟩:=Finset.exists_ne_zero_of_sum_ne_zero hne
  split_ifs at hz with hpart
  · obtain ⟨I,hI,hIs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hz
    obtain ⟨J,hJ,hterm⟩:=Finset.exists_ne_zero_of_sum_ne_zero hIs
    have hcoeff: (β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J)≠0:=
      (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hterm).1).2
    have hl:β (C*I)≠0:=(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hcoeff).1).1
    have hr:β (D*J)≠0:=by
      intro hh
      exact hcoeff (by rw [hh,zero_mul,star_zero,mul_zero])
    have hk: ((_:ℂ)*((_:ℝ):ℂ))≠0:=(mul_ne_zero_iff.mp hterm).2
    have hw: (_:ℝ)≠0:=Complex.ofReal_ne_zero.mp (mul_ne_zero_iff.mp hk).2
    exact ⟨I,J,hl,hr,(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hw).1).2,(mul_ne_zero_iff.mp hw).2⟩
  · exact False.elim (hz rfl)

 theorem physicalBlock_scale_lower (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (U:Finset (CommonIndex C D)) (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ)
    (a H:ℝ) (ha:0<a) (hlower:∀I:Ideal O,β I≠0→a*H≤(Ideal.absNorm I:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    H/(Ideal.absNorm C:ℝ)≤dyadicScale (n 2)/a ∧
      H/(Ideal.absNorm D:ℝ)≤dyadicScale (n 3)/a := by
  obtain ⟨I,J,hI,hJ,hwi,hwj⟩:=physicalBlock_column_witnesses η t S β C D hC hD U R rows W K n hne
  exact ⟨raw_window_lower C I hC.1 a H ha (n 2) (hlower _ hI) hwi,
    raw_window_lower D J hD.1 a H ha (n 3) (hlower _ hJ) hwj⟩

end SevenEighths.CenteredMomentSourceBlockWindows

end

end OAI
