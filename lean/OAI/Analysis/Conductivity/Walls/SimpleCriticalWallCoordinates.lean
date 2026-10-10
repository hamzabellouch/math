import Mathlib
import OAI.Analysis.Conductivity.Walls.CriticalWallTensor
import OAI.Analysis.Conductivity.Variational.ParametricAxialNormalization
import OAI.Analysis.Conductivity.Fourier.PureModeWall

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_simple_critical_wall_coordinates
    {u v : P×Coord3 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (p : P)
    {σ lam k : ℝ} (hσ : σ≠0) (hk : k≠0)
    (hub : ∀ y,u (p,y)=y 0)
    (hvb : ∀ y,v (p,y)=pureWallMode σ lam k (boxCoordinates y))
    {x : Coord3} (_ : x 2=0)
    {U : Set Coord3} (hU : IsOpen U) (hx : x∈U) :
    ∃ Y : OpenPartialHomeomorph (P×Coord3) (P×Coord3),
      (p,x)∈Y.source ∧ Y.source⊆univ×ˢU ∧
      (∀ q y,(Y (q,y)).1=q) ∧ (∀ y,Y (p,y)=(p,y)) ∧
      ContDiff ℝ (↑(⊤:ℕ∞)) Y ∧ ContDiffOn ℝ (↑(⊤:ℕ∞)) Y.symm Y.target ∧
      ∃ w : P×Box3 → ℝ,ContDiff ℝ (↑(⊤:ℕ∞)) w ∧
        (∀ y,w (p,y)=pureWallMode σ lam k y) ∧
        (∀ q z,wallDerivative (fun y => w (q,y)) (z,0)=0) ∧
        ∀ z∈Y.source,wallCoordinatePair (fun y => w (z.1,y)) (Y z).2=![u z,v z] := by
  let V : Coord3 → ℝ := pureWallMode σ lam k∘boxCoordinates
  have hVs : ContDiff ℝ (↑(⊤:ℕ∞)) V := (pureWallMode_smooth σ lam k).comp boxCoordinates.contDiff
  obtain ⟨A,hAs,hA,hAsm,hAi,w₀,hw₀,hw₀b,hw₀e⟩ :=
    exists_parametric_axial_normalization hu hv p x hVs hub hvb
  let wB : P×Box3 → ℝ := fun z => w₀ (z.1,boxCoordinates.symm z.2)
  have hwB : ContDiff ℝ (↑(⊤:ℕ∞)) wB :=
    hw₀.comp (contDiff_fst.prodMk (boxCoordinates.symm.contDiff.comp contDiff_snd))
  have hwBb : (fun y => wB (p,y))=pureWallMode σ lam k := by
    funext y
    simp only [wB,hw₀b,V,Function.comp_apply,boxCoordinates.apply_symm_apply]
  have hwBz : ∀ y,wallDerivative (fun z => wB (p,z)) (y,0)=0 := by
    rw [hwBb]; exact pureWallMode_wall_critical σ lam k
  have hwBn : wallDerivative (wallDerivative (fun z => wB (p,z))) ((x 0,x 1),0)≠0 := by
    rw [hwBb]; exact pureWallMode_wall_simple hσ hk _
  obtain ⟨ρ,hρ,hρ₀,w,hw,hwb,hwz,hwe⟩ := exists_recentered_critical_wall hwB p (x 0,x 1) hwBz hwBn
  let Q : P×Coord3 → P×(ℝ×ℝ) := fun z => (z.1,(u z,z.2 1))
  have hQ : ContDiff ℝ (↑(⊤:ℕ∞)) Q := contDiff_fst.prodMk
    (hu.prodMk ((contDiff_apply ℝ ℝ (1:Fin 3)).comp contDiff_snd))
  let φ : P×Coord3 → Coord3 := fun z => ![u z,z.2 1,z.2 2-ρ (Q z)]
  have hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · change ContDiff ℝ (↑(⊤:ℕ∞)) u
      exact hu
    · change ContDiff ℝ (↑(⊤:ℕ∞)) (fun z : P×Coord3 => z.2 1)
      exact (contDiff_apply ℝ ℝ (1:Fin 3)).comp contDiff_snd
    · change ContDiff ℝ (↑(⊤:ℕ∞)) (fun z : P×Coord3 => z.2 2-ρ (Q z))
      exact ((contDiff_apply ℝ ℝ (2:Fin 3)).comp contDiff_snd).sub (hρ.comp hQ)
  have hφb (y : Coord3) : φ (p,y)=y := by
    ext i
    fin_cases i <;> simp [φ,Q,hub,hρ₀]
  have hQt : Tendsto Q (𝓝 (p,x)) (𝓝 (p,(x 0,x 1))) := by
    simpa only [Q,hub] using hQ.continuous.tendsto (p,x)
  have he : ∀ᶠ z in 𝓝 (p,x),wallCoordinatePair (fun y => w (z.1,y)) (φ z)=![u z,v z] := by
    filter_upwards [hw₀e,hQt.eventually hwe] with z haz hwz'
    ext i
    fin_cases i
    · rfl
    · change w (z.1,((u z,z.2 1),z.2 2-ρ (Q z)))=v z
      rw [hwz' (z.2 2-ρ (Q z))]
      simp only [Q,sub_add_cancel,wB]
      change w₀ (z.1,![u z,z.2 1,z.2 2])=v z
      simpa only [hA] using haz
  obtain ⟨N,hN,hNo,hpN⟩ := mem_nhds_iff.mp he
  have hL : fderiv ℝ (fun y => φ (p,y)) x=(ContinuousLinearEquiv.refl ℝ Coord3 : Coord3 →L[ℝ] Coord3) := by
    rw [show (fun y => φ (p,y))=id from funext hφb,fderiv_id]
    rfl
  obtain ⟨Y,hYs,hYN,hY,hsm,hinv⟩ := exists_parametric_diffeomorph hφ p x
    (ContinuousLinearEquiv.refl ℝ Coord3) hL (hNo.inter (isOpen_univ.prod hU)) ⟨hpN,mem_univ p,hx⟩
  refine ⟨Y,hYs,fun z hz => (hYN hz).2,fun q y => by simp only [hY],
    fun y => by rw [hY,hφb],hsm,hinv,w,hw,?_,hwz,?_⟩
  · intro y
    exact (hwb y).trans (congrFun hwBb y)
  · intro z hz
    rw [hY]
    exact hN (hYN hz).1

end ScalarConductivity

end
end

end OAI
