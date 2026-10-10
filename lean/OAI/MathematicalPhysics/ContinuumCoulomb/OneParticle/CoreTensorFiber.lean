import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.LastTensorFiber
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.FullSpinTensorCoefficients
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoreOrbitalProjection
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RealSpinOrbitals
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.OneElectronClosure
import OAI.Analysis.CoulombRadii.FieldAnalysis.SpinConfigurationIntegral

namespace OAI

/-! The last-coordinate contraction in full spin space is exactly the
core-slice orbital coefficient used by the many-electron energy bound. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

def spinConfigurationPoint {n : ℕ} (s : SpinConfiguration n) (x : Configuration n) :
    Fin n → Fin 2 × (Fin 3 → ℝ) := fun i => (s i,fun a => x (i,a))

theorem spinConfigurationPoint_coordinates {n : ℕ}
    (z : Fin n → Fin 2 × (Fin 3 → ℝ)) :
    spinConfigurationPoint ((Coulomb.spinCubeEquiv n) z).1
      (WithLp.toLp 2 ((Coulomb.spinCubeEquiv n) z).2) = z := by
  rfl

theorem cubeState_snoc {n : ℕ} (u : Coulomb.H1Vector (n+1))
    (s : SpinConfiguration n) (x : Configuration n) (t : Fin 2) (y : Configuration 1) :
    Coulomb.cubeState u (Fin.snoc (spinConfigurationPoint s x)
      (t,fun a => y (0,a))) =
    u.value (Fin.append s (fun _ => t)) (Coulomb.joinConfiguration n 1 (x,y)) := by
  unfold Coulomb.cubeState
  congr 1
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Fin.append_right_eq_snoc]
    · simp [Fin.append_right_eq_snoc,spinConfigurationPoint]
  · apply PiLp.ext
    intro a
    obtain ⟨i,b⟩ := a
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]
      change y (0,b) = Coulomb.joinConfiguration n 1 (x,y) (Fin.last n,b)
      simpa only [show Fin.natAdd n (0:Fin 1) = Fin.last n from Fin.ext rfl] using
        (Coulomb.joinConfiguration_right n 1 x y (0:Fin 1) b).symm
    · simp only [Fin.snoc_castSucc]
      change x (j,b) = Coulomb.joinConfiguration n 1 (x,y) (j.castSucc,b)
      simpa only [show Fin.castAdd 1 j = j.castSucc from Fin.ext rfl] using
        (Coulomb.joinConfiguration_left n 1 x y j b).symm

theorem lastTensorFiber_coreSlice {n : ℕ} (u : Coulomb.H1Vector (n+1))
    (s : SpinConfiguration n) (x : Configuration n) (hx : u.CoreSliceRegular s x)
    (z : Fin 2 × (Fin 3 → ℝ)) :
    lastTensorFiber (Coulomb.cubeState u) (spinConfigurationPoint s x,z) =
      Coulomb.flatSpinOrbital (fun y t => (u.coreSlice s x).value (fun _ => t)
        (oneElectronCoordinates.symm y)) z := by
  change Coulomb.cubeState u (Fin.snoc (spinConfigurationPoint s x) z) =
    (u.coreSlice s x).value (fun _ => z.1) (oneElectronCoordinates.symm (WithLp.toLp 2 z.2))
  rw [u.coreSlice_value s hx]
  have hz : (z.1,fun a => oneElectronCoordinates.symm (WithLp.toLp 2 z.2) (0,a)) = z := by
    exact Prod.ext rfl rfl
  simpa only [hz] using cubeState_snoc u s x z.1
    (oneElectronCoordinates.symm (WithLp.toLp 2 z.2))

theorem coreOrbitalCoefficient_slice {n : ℕ} (u : Coulomb.H1Vector (n+1))
    (φ : Lp ℂ 2 (volume : Measure (Configuration 1)))
    (s : SpinConfiguration n) (x : Configuration n) (hx : u.CoreSliceRegular s x)
    (t : SpinConfiguration 1) :
    coreOrbitalCoefficient u φ s t x =
      inner ℂ φ (h1Coordinates (u.coreSlice s x) (Sum.inl t)) := by
  rw [h1_inner_orbital]
  simp only [u.coreSlice_value s hx,coreOrbitalCoefficient]

theorem lastTensorFiber_realOrbital_core {n : ℕ} (u : Coulomb.H1Vector (n+1))
    (f : Position → ℝ) (hf : MemLp f 2) (σ : Fin 2)
    (s : SpinConfiguration n) (x : Configuration n) (hx : u.CoreSliceRegular s x) :
    Coulomb.fiberContract (μ := Coulomb.spinSpaceMeasure)
      (Coulomb.flatSpinOrbital (realSpinOrbital f σ)) (lastTensorFiber (Coulomb.cubeState u))
      (spinConfigurationPoint s x) =
    coreOrbitalCoefficient u (oneElectronOrbitalLp f hf) s (fun _ => σ) x := by
  let w (y : Position) (t : Fin 2) :=
    (u.coreSlice s x).value (fun _ => t) (oneElectronCoordinates.symm y)
  have hw (t : Fin 2) : MemLp (fun y => w y t) 2 :=
    ((u.coreSlice s x).value_L2 (fun _ => t)).comp_measurePreserving
      oneElectronCoordinates.symm.measurePreserving
  have he : Coulomb.fiberContract (μ := Coulomb.spinSpaceMeasure)
      (Coulomb.flatSpinOrbital (realSpinOrbital f σ)) (lastTensorFiber (Coulomb.cubeState u))
        (spinConfigurationPoint s x) =
      ∫ z, star (Coulomb.flatSpinOrbital (realSpinOrbital f σ) z)*Coulomb.flatSpinOrbital w z
        ∂Coulomb.spinSpaceMeasure := by
    unfold Coulomb.fiberContract
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => congrArg (fun c =>
      star (Coulomb.flatSpinOrbital (realSpinOrbital f σ) z)*c)
        (lastTensorFiber_coreSlice u s x hx z))
  rw [he,Coulomb.flatSpinOrbital_inner _ w (realSpinOrbital_memLp f hf σ) hw]
  have hsum : (∑ t : Fin 2, ∫ y, star (realSpinOrbital f σ y t)*w y t) =
      ∫ y, (f y:ℂ)*w y σ := by
    have hpoint (t : Fin 2) : (∫ y, star (realSpinOrbital f σ y t)*w y t) =
        if t=σ then (∫ y, (f y:ℂ)*w y σ) else 0 := by
      by_cases ht : t=σ
      · subst t
        simp only [realSpinOrbital,ite_true,Complex.star_def,Complex.conj_ofReal]
      · simp only [realSpinOrbital,ht,ite_false,star_zero,zero_mul,integral_zero]
    simp only [hpoint]
    simp
  rw [hsum,coreOrbitalCoefficient_slice u _ s x hx,oneElectron_inner_real_orbital]
  rw [← oneElectronCoordinates_integral_complex (fun y => (f y:ℂ)*w y σ)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    dsimp [w]
    rw [LinearIsometryEquiv.symm_apply_apply]
    ring)

theorem lastTensorFiber_realOrbital_integral {n : ℕ} (u : Coulomb.H1Vector (n+1))
    (f : Position → ℝ) (hf : MemLp f 2) (σ : Fin 2) :
    (∫ y, ‖Coulomb.fiberContract (μ := Coulomb.spinSpaceMeasure)
      (Coulomb.flatSpinOrbital (realSpinOrbital f σ)) (lastTensorFiber (Coulomb.cubeState u)) y‖^2
      ∂(Measure.pi fun _ : Fin n => Coulomb.spinSpaceMeasure)) =
    ∑ s, ∫ x, ‖coreOrbitalCoefficient u (oneElectronOrbitalLp f hf) s (fun _ => σ) x‖^2 := by
  have hs (s : SpinConfiguration n) :=
    (PiLp.volume_preserving_toLp (Fin n × Fin 3)).quasiMeasurePreserving.ae
      (u.coreSliceRegular_ae s)
  have hp := (Measure.quasiMeasurePreserving_snd
    (μ := (Measure.count : Measure (SpinConfiguration n)))).ae (ae_all_iff.mpr hs)
  have ht := (Coulomb.spinCubeEquiv_full_measurePreserving n).quasiMeasurePreserving.ae hp
  have he : (fun y => ‖Coulomb.fiberContract (μ := Coulomb.spinSpaceMeasure)
      (Coulomb.flatSpinOrbital (realSpinOrbital f σ)) (lastTensorFiber (Coulomb.cubeState u)) y‖^2) =ᵐ[
        Measure.pi fun _ : Fin n => Coulomb.spinSpaceMeasure]
      fun y => ‖coreOrbitalCoefficient u (oneElectronOrbitalLp f hf)
        ((Coulomb.spinCubeEquiv n) y).1 (fun _ => σ)
        (WithLp.toLp 2 ((Coulomb.spinCubeEquiv n) y).2)‖^2 := by
    filter_upwards [ht] with y hy
    have h := lastTensorFiber_realOrbital_core u f hf σ
      ((Coulomb.spinCubeEquiv n) y).1 (WithLp.toLp 2 ((Coulomb.spinCubeEquiv n) y).2)
      (hy ((Coulomb.spinCubeEquiv n) y).1)
    rw [spinConfigurationPoint_coordinates] at h
    exact congrArg (fun z : ℂ => ‖z‖^2) h
  rw [integral_congr_ae he]
  exact Coulomb.spinConfiguration_integral _ (fun s =>
    (coreOrbitalCoefficient_memLp u (oneElectronOrbitalLp f hf) s (fun _ => σ)).norm.integrable_sq)

theorem coreOrbitalMass_last_occupation {n : ℕ} {ι : Type*} [Fintype ι]
    (u : Coulomb.H1Vector (n+1)) (f : ι → Position → ℝ) (hf : ∀ i, MemLp (f i) 2) :
    coreOrbitalMass u (fun i => oneElectronOrbitalLp (f i) (hf i)) =
    ∑ i, ∑ σ : Fin 2, ∫ y, ‖Coulomb.fiberContract (μ := Coulomb.spinSpaceMeasure)
      (Coulomb.flatSpinOrbital (realSpinOrbital (f i) σ)) (lastTensorFiber (Coulomb.cubeState u)) y‖^2
      ∂(Measure.pi fun _ : Fin n => Coulomb.spinSpaceMeasure) := by
  rw [coreOrbitalMass_eq_coefficients]
  have he (i : ι) (σ : Fin 2) := lastTensorFiber_realOrbital_integral u (f i) (hf i) σ
  simp_rw [he]
  symm
  calc
    _ = ∑ i, ∑ s, ∑ σ : Fin 2, ∫ x,
        ‖coreOrbitalCoefficient u (oneElectronOrbitalLp (f i) (hf i)) s (fun _ => σ) x‖^2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ s, ∑ i, ∑ σ : Fin 2, ∫ x,
        ‖coreOrbitalCoefficient u (oneElectronOrbitalLp (f i) (hf i)) s (fun _ => σ) x‖^2 :=
      Finset.sum_comm
    _ = ∑ s, ∑ σ : Fin 2, ∑ i, ∫ x,
        ‖coreOrbitalCoefficient u (oneElectronOrbitalLp (f i) (hf i)) s (fun _ => σ) x‖^2 := by
      apply Finset.sum_congr rfl
      intro s _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      exact (Equiv.funUnique (Fin 1) (Fin 2)).symm.sum_comp
        (fun t : SpinConfiguration 1 => ∑ i, ∫ x,
          ‖coreOrbitalCoefficient u (oneElectronOrbitalLp (f i) (hf i)) s t x‖^2)

theorem coreOrbitalMass_first_occupation {n : ℕ} {ι : Type*} [Fintype ι]
    (u : Coulomb.H1Vector (n+1)) (hu : Coulomb.Antisymmetric u)
    (f : ι → Position → ℝ) (hf : ∀ i, MemLp (f i) 2) :
    coreOrbitalMass u (fun i => oneElectronOrbitalLp (f i) (hf i)) =
    ∑ i, ∑ σ : Fin 2, ∫ y, ‖Coulomb.fiberContract (μ := Coulomb.spinSpaceMeasure)
      (Coulomb.flatSpinOrbital (realSpinOrbital (f i) σ)) (Coulomb.firstFiber (Coulomb.cubeState u)) y‖^2
      ∂(Measure.pi fun _ : Fin n => Coulomb.spinSpaceMeasure) := by
  rw [coreOrbitalMass_last_occupation u f hf]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro σ _
  exact last_first_fiber_norm_integral _ (fullSpin_antisymmetric u hu) _

end ContinuumCoulomb

end

end OAI
