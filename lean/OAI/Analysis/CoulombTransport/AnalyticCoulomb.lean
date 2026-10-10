import OAI.Analysis.CoulombTransport.Model

namespace OAI

universe uE uF uP uS uR

noncomputable section

namespace Problem356.AnalyticCoulomb

/-- Inverse distance is real analytic off the diagonal; the statement
also supplies every finite or infinite differentiability order. -/
theorem contDiffAt_inverseDistance {E : Type uE} {F : Type uF}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {n : WithTop ENat} {f g : E → F} {x : E}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x)
    (hne : f x ≠ g x) :
    ContDiffAt ℝ n (fun y => ‖f y - g y‖⁻¹) x := by
  exact ((hf.sub hg).norm ℝ (sub_ne_zero.mpr hne)).inv
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne))

/-- The real-valued Coulomb formula is analytic at every collision-free triple. -/
theorem contDiffAt_cost {n : WithTop ENat} (t : Triple)
    (h12 : t.1 ≠ t.2.1) (h13 : t.1 ≠ t.2.2) (h23 : t.2.1 ≠ t.2.2) :
    ContDiffAt ℝ n (fun p : Triple =>
      ‖p.1 - p.2.1‖⁻¹ + ‖p.1 - p.2.2‖⁻¹ + ‖p.2.1 - p.2.2‖⁻¹) t := by
  have h1 : ContDiffAt ℝ n (fun p : Triple => p.1) t := contDiffAt_fst
  have h2 : ContDiffAt ℝ n (fun p : Triple => p.2.1) t := contDiffAt_snd.fst
  have h3 : ContDiffAt ℝ n (fun p : Triple => p.2.2) t := contDiffAt_snd.snd
  exact ((contDiffAt_inverseDistance h1 h2 h12).add
    (contDiffAt_inverseDistance h1 h3 h13)).add
    (contDiffAt_inverseDistance h2 h3 h23)

/-- Analyticity of a parameter-dependent partial derivative.  This is the
stationarity-map regularity needed by the analytic implicit-function theorem. -/
theorem contDiffAt_partialFDeriv {P : Type uP} {S : Type uS} {R : Type uR}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup S] [NormedSpace ℝ S]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    {F : P × S → R} {p : P × S}
    (hF : ContDiffAt ℝ (⊤ : WithTop ENat) F p) :
    ContDiffAt ℝ (⊤ : WithTop ENat)
      (fun q : P × S => fderiv ℝ (fun s => F (q.1, s)) q.2) p := by
  have hpair : ContDiffAt ℝ (⊤ : WithTop ENat)
      (fun q : (P × S) × S => (q.1.1, q.2)) (p, p.2) :=
    contDiffAt_fst.fst.prodMk contDiffAt_snd
  have hcomp : ContDiffAt ℝ (⊤ : WithTop ENat)
      (Function.uncurry (fun (q : P × S) (s : S) => F (q.1, s))) (p, p.2) :=
    hF.comp _ hpair
  exact hcomp.fderiv contDiffAt_snd le_top

/-- Joint analyticity of the state Hessian, hence its continuity for the
positive-definiteness persistence step. -/
theorem contDiffAt_partialHessian {P : Type uP} {S : Type uS} {R : Type uR}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup S] [NormedSpace ℝ S]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    {F : P × S → R} {p : P × S}
    (hF : ContDiffAt ℝ (⊤ : WithTop ENat) F p) :
    ContDiffAt ℝ (⊤ : WithTop ENat)
      (fun q : P × S => fderiv ℝ
        (fun s => fderiv ℝ (fun r => F (q.1, r)) s) q.2) p := by
  exact contDiffAt_partialFDeriv (contDiffAt_partialFDeriv hF)

/-- In parameter/state coordinates `(y,(x,z))`, subtracting arbitrary analytic
central and outer potentials leaves an analytic Coulomb stationarity map. -/
theorem contDiffAt_stationarity
    (u v : E3 → ℝ) (p : E3 × (E3 × E3))
    (hu : ContDiffAt ℝ (⊤ : WithTop ENat) u p.2.1)
    (hv : ContDiffAt ℝ (⊤ : WithTop ENat) v p.2.2)
    (hxy : p.2.1 ≠ p.1) (hxz : p.2.1 ≠ p.2.2) (hyz : p.1 ≠ p.2.2) :
    ContDiffAt ℝ (⊤ : WithTop ENat)
      (fun q : E3 × (E3 × E3) =>
        fderiv ℝ (fun s : E3 × E3 =>
          ‖s.1 - q.1‖⁻¹ + ‖s.1 - s.2‖⁻¹ + ‖q.1 - s.2‖⁻¹ - u s.1 - v s.2)
          q.2) p := by
  apply contDiffAt_partialFDeriv (F := fun q : E3 × (E3 × E3) =>
    ‖q.2.1 - q.1‖⁻¹ + ‖q.2.1 - q.2.2‖⁻¹ + ‖q.1 - q.2.2‖⁻¹ - u q.2.1 - v q.2.2)
  have hx : ContDiffAt ℝ (⊤ : WithTop ENat) (fun q : E3 × (E3 × E3) => q.2.1) p :=
    contDiffAt_snd.fst
  have hy : ContDiffAt ℝ (⊤ : WithTop ENat) (fun q : E3 × (E3 × E3) => q.1) p :=
    contDiffAt_fst
  have hz : ContDiffAt ℝ (⊤ : WithTop ENat) (fun q : E3 × (E3 × E3) => q.2.2) p :=
    contDiffAt_snd.snd
  exact ((((contDiffAt_inverseDistance hx hy hxy).add
    (contDiffAt_inverseDistance hx hz hxz)).add
    (contDiffAt_inverseDistance hy hz hyz)).sub (hu.comp p hx)).sub (hv.comp p hz)

end Problem356.AnalyticCoulomb

end

end OAI
