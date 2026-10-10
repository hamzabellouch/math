import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFullBoundaryError
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralShellAbsorption

namespace OAI

/-! Exact scalar Green data, and the resulting two-channel outgoing boundary
estimate. The remote error is measured against the two endpoint values. -/

open Set
namespace DefocusingNLS

structure SpectralScalarBoundarySystem (R E A : ℝ) where
  k : ℝ → ℝ
  V : ℝ → ℂ
  beta : ℂ
  D : ℝ → ℂ × ℂ
  U : ℝ → ℂ × ℂ
  W : ℂ
  continuous_k : ContinuousOn k (Icc R E)
  positive_k : ∀ r ∈ Icc R E, 0 < k r
  continuous_D : ContinuousOn D (Icc R E)
  continuous_U : ContinuousOn U (Icc R E)
  ode_D : ∀ r ∈ Icc R E, HasDerivAt D (spectralScalarField (V r) (D r)) r
  ode_U : ∀ r ∈ Icc R E, HasDerivAt U (spectralScalarField (V r) (U r)) r
  left_D : (D R).1 = 0
  left_U : (U R).1 ≠ 0
  right_U : (U E).2 = beta*(U E).1
  wronskian_ne : W ≠ 0
  wronskian : ∀ r ∈ Icc R E, spectralScalarWronskian (D r) (U r) = W
  green : ∀ r ∈ Icc R E, ∀ t ∈ Icc R E,
    spectralShellNorm (k r) (spectralScalarGreenState D U W r t) ≤ A/k t

noncomputable def SpectralScalarBoundarySystem.extension {R E A : ℝ}
    (S : SpectralScalarBoundarySystem R E A) (z : ℂ) (r : ℝ) : ℂ × ℂ :=
  (z/(S.U R).1) • S.U r

theorem SpectralScalarBoundarySystem.error_bound {R E A : ℝ}
    (S : SpectralScalarBoundarySystem R E A) (kap C B M r : ℝ)
    (hR : 0 < R) (hr : r ∈ Icc R E) (hkap : 0 < kap) (hA : 0 ≤ A)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hk : ∀ t ∈ Icc R E, kap ≤ S.k t)
    (q : ℝ → ℂ × ℂ) (f : ℝ → ℂ)
    (hqc : ContinuousOn q (Icc R E)) (hfc : ContinuousOn f (Icc R E))
    (hq : ∀ t ∈ Icc R E, HasDerivAt q (spectralScalarField (S.V t) (q t)+(0,f t)) t)
    (hforcing : ∀ t ∈ Icc R E, ‖f t‖ ≤ C/(kap*t^2)*M)
    (hboundary : ‖(q E).2-S.beta*(q E).1‖ ≤ B/kap*M) :
    spectralShellNorm (S.k r) (q r-S.extension (q R).1 r) ≤
      ((A+1)*(B+C/R)/kap^2)*M :=
  spectralScalar_full_boundary_error R E r kap A C B M hR hr hkap hA hC hM
    S.k hk S.D S.U q S.V f S.W S.beta S.continuous_D S.continuous_U hqc hfc
    S.wronskian_ne S.wronskian S.ode_D S.ode_U hq S.left_D S.left_U S.right_U
    (S.green r hr) hforcing hboundary

theorem spectralCoupled_boundary_error {R E A : ℝ}
    (Sp Sm : SpectralScalarBoundarySystem R E A) (kap C B M r : ℝ)
    (hR : 0 < R) (hr : r ∈ Icc R E) (hkap : 0 < kap)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hkp : ∀ t ∈ Icc R E, kap ≤ Sp.k t) (hkm : ∀ t ∈ Icc R E, kap ≤ Sm.k t)
    (q : ℝ → (ℂ × ℂ) × (ℂ × ℂ)) (fp fm : ℝ → ℂ)
    (hqc : ContinuousOn q (Icc R E))
    (hfp : ContinuousOn fp (Icc R E)) (hfm : ContinuousOn fm (Icc R E))
    (hqp : ∀ t ∈ Icc R E, HasDerivAt (fun s => (q s).1)
      (spectralScalarField (Sp.V t) (q t).1+(0,fp t)) t)
    (hqm : ∀ t ∈ Icc R E, HasDerivAt (fun s => (q s).2)
      (spectralScalarField (Sm.V t) (q t).2+(0,fm t)) t)
    (hforcingp : ∀ t ∈ Icc R E, ‖fp t‖ ≤ C/(kap*t^2)*M)
    (hforcingm : ∀ t ∈ Icc R E, ‖fm t‖ ≤ C/(kap*t^2)*M)
    (hbound : spectralShellPairNorm (Sp.k E) (Sm.k E) (q E) ≤ M)
    (hremote : max ‖(q E).1.2-Sp.beta*(q E).1.1‖ ‖(q E).2.2-Sm.beta*(q E).2.1‖ ≤
      B/E*max ‖(q E).1.1‖ ‖(q E).2.1‖) :
    spectralShellPairNorm (Sp.k r) (Sm.k r)
      (q r-(Sp.extension (q R).1.1 r,Sm.extension (q R).2.1 r)) ≤
      ((A+1)*(B/E+C/R)/kap^2)*M := by
  have hRE : R ≤ E := hr.1.trans hr.2
  have hE : 0 < E := hR.trans_le hRE
  have hvals := spectralShellPairNorm_values (Sp.k E) (Sm.k E) kap hkap
    (hkp E ⟨hRE,le_rfl⟩) (hkm E ⟨hRE,le_rfl⟩) (q E)
  have hv : max ‖(q E).1.1‖ ‖(q E).2.1‖ ≤ M/kap := max_le
    (hvals.1.trans (div_le_div_of_nonneg_right hbound hkap.le))
    (hvals.2.trans (div_le_div_of_nonneg_right hbound hkap.le))
  have hrem : max ‖(q E).1.2-Sp.beta*(q E).1.1‖ ‖(q E).2.2-Sm.beta*(q E).2.1‖ ≤
      (B/E)/kap*M := by
    calc
      _ ≤ B/E*max ‖(q E).1.1‖ ‖(q E).2.1‖ := hremote
      _ ≤ B/E*(M/kap) := mul_le_mul_of_nonneg_left hv (div_nonneg hB hE.le)
      _ = _ := by ring
  have hp := Sp.error_bound kap C (B/E) M r hR hr hkap hA hC hM hkp
    (fun t => (q t).1) fp hqc.fst hfp hqp hforcingp ((le_max_left _ _).trans hrem)
  have hm := Sm.error_bound kap C (B/E) M r hR hr hkap hA hC hM hkm
    (fun t => (q t).2) fm hqc.snd hfm hqm hforcingm ((le_max_right _ _).trans hrem)
  exact max_le hp hm

theorem spectralCoupled_boundary_absorb {R E A : ℝ}
    (Sp Sm : SpectralScalarBoundarySystem R E A) (kap C B L : ℝ)
    (hR : 0 < R) (hRE : R ≤ E) (hkap : 0 < kap)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hsmall : (A+1)*(B/E+C/R)/kap^2 ≤ 1/2)
    (hkp : ∀ t ∈ Icc R E, kap ≤ Sp.k t) (hkm : ∀ t ∈ Icc R E, kap ≤ Sm.k t)
    (q : ℝ → (ℂ × ℂ) × (ℂ × ℂ)) (fp fm : ℝ → ℂ)
    (hqc : ContinuousOn q (Icc R E))
    (hfp : ContinuousOn fp (Icc R E)) (hfm : ContinuousOn fm (Icc R E))
    (hqp : ∀ t ∈ Icc R E, HasDerivAt (fun s => (q s).1)
      (spectralScalarField (Sp.V t) (q t).1+(0,fp t)) t)
    (hqm : ∀ t ∈ Icc R E, HasDerivAt (fun s => (q s).2)
      (spectralScalarField (Sm.V t) (q t).2+(0,fm t)) t)
    (hforcingp : ∀ t ∈ Icc R E, ‖fp t‖ ≤ C/(kap*t^2)*spectralShellPairNorm (Sp.k t) (Sm.k t) (q t))
    (hforcingm : ∀ t ∈ Icc R E, ‖fm t‖ ≤ C/(kap*t^2)*spectralShellPairNorm (Sp.k t) (Sm.k t) (q t))
    (hremote : max ‖(q E).1.2-Sp.beta*(q E).1.1‖ ‖(q E).2.2-Sm.beta*(q E).2.1‖ ≤
      B/E*max ‖(q E).1.1‖ ‖(q E).2.1‖)
    (hext : ∀ r ∈ Icc R E, spectralShellPairNorm (Sp.k r) (Sm.k r)
      (Sp.extension (q R).1.1 r,Sm.extension (q R).2.1 r) ≤ L) :
    ∀ r ∈ Icc R E,
      spectralShellPairNorm (Sp.k r) (Sm.k r) (q r) ≤ 2*L ∧
      spectralShellPairNorm (Sp.k r) (Sm.k r)
        (q r-(Sp.extension (q R).1.1 r,Sm.extension (q R).2.1 r)) ≤
          2*((A+1)*(B/E+C/R)/kap^2)*L := by
  have hE : 0 < E := hR.trans_le hRE
  apply spectralShellPairNorm_absorb R E L ((A+1)*(B/E+C/R)/kap^2) hRE
    (by positivity) hsmall Sp.k Sm.k q
    (fun r => (Sp.extension (q R).1.1 r,Sm.extension (q R).2.1 r))
    Sp.continuous_k Sm.continuous_k Sp.positive_k Sm.positive_k hqc hext
  intro M hM hbound r hr
  exact spectralCoupled_boundary_error Sp Sm kap C B M r hR hr hkap hA hC hB hM hkp hkm q fp fm
    hqc hfp hfm hqp hqm
    (fun t ht => (hforcingp t ht).trans
      (mul_le_mul_of_nonneg_left (hbound t ht) (by positivity)))
    (fun t ht => (hforcingm t ht).trans
      (mul_le_mul_of_nonneg_left (hbound t ht) (by positivity)))
    (hbound E ⟨hRE,le_rfl⟩) hremote

theorem SpectralScalarBoundarySystem.inner_slope_bound {R E A : ℝ}
    (S : SpectralScalarBoundarySystem R E A) (hRE : R ≤ E) (q : ℂ × ℂ) (eps : ℝ)
    (herror : spectralShellNorm (S.k R) (q-S.extension q.1 R) ≤ eps) :
    ‖q.2-((S.U R).2/(S.U R).1)*q.1‖ ≤ S.k R*eps := by
  have hk := S.positive_k R ⟨le_rfl,hRE⟩
  have hs := spectralShellNorm_slope (S.k R) hk (q-S.extension q.1 R)
  have he : (q-S.extension q.1 R).2 = q.2-((S.U R).2/(S.U R).1)*q.1 := by
    dsimp only [SpectralScalarBoundarySystem.extension,Prod.smul_snd,Prod.snd_sub,smul_eq_mul]
    ring
  rw [he] at hs
  exact hs.trans (mul_le_mul_of_nonneg_left herror hk.le)

end DefocusingNLS

end OAI
