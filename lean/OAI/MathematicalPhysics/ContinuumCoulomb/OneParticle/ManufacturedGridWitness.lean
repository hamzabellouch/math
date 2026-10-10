import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.NuclearQuadratureScale

namespace OAI

/-! One actual transport supplies both the full weak-H1 error and the
uncut orbital entries, with uniform constants at the physical mesh. -/

noncomputable section
open MeasureTheory
open scoped NNReal
namespace ContinuumCoulomb

theorem manufactured_grid_witness (hp : PublishedC4FlowInput) :
    ∃ rho : ℕ, 0 < rho ∧ ∃ L K : ℝ≥0, 0 < L ∧ 0 < K ∧ ∃ D : ℝ, 1 ≤ D ∧
    ∀ freq : ℝ, 0 < freq → ∃ E : ℝ, 1 ≤ E ∧
    ∀ R scale S H : ℝ, 2 ≤ R → 0 < scale → R^5 ≤ S → S ≤ 2*R^5 → 0 ≤ H →
    ∀ (m : ℕ) (u : Fin m → PlanarPosition), (m:ℝ) ≤ R^14 →
    (∀ i j, i ≠ j → 3 ≤ ‖u i-u j‖) →
    (∀ i, localizedCounterterm freq u i ≤ scale) →
    tsupport (manufacturedWellField freq scale S u) ⊆ slabDomain H S →
    ∀ {ι : Type} [Fintype ι] (index : ι → Fin 3 → ℤ), Function.Injective index →
    (⋃ i, positionCube (gaussCellCenter (1/R^10) (index i)) (1/R^10)) = slabDomain H S →
    ∃ G : Position → ℝ → Position,
      IsUnitTimeFlow (moserVelocity rho (manufacturedWellField freq scale S u)) G ∧
      Function.Bijective (fun x => G x 1) ∧
      LipschitzWith L (fun x => G x 1) ∧ AntilipschitzWith K (fun x => G x 1) ∧
      (∀ x, x ∉ tsupport (manufacturedWellField freq scale S u) → G x 1 = x) ∧
      (∀ x, |manufacturedCharge (manufacturedWellField freq scale S u) x| ≤ (rho:ℝ)/2) ∧
      ContDiff ℝ 4 (fun x => G x 1) ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k (fun y => G y 1) x‖ ≤ L) ∧
      let F : Position → ℝ := fun y => gridNuclearPotential index (fun x => G x 1) rho (1/R^10) y-
        (slabPotential rho H S y+manufacturedWellField freq scale S u y)
      (∀ (n : ℕ) (w : Coulomb.H1Vector n) (s : SpinConfiguration n) (i : Fin n),
        Integrable (fun x => |F (Coulomb.position x i)| *‖w.value s x‖^2) ∧
        (∫ x, |F (Coulomb.position x i)| *‖w.value s x‖^2) ≤
          (D/R^20)*((∫ x, ‖w.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖w.gradient s (i,k) x‖^2)) ∧
      (∀ v w : PlanarPosition,
        Integrable (fun y => F y*continuumLocalizedMode freq v y*continuumLocalizedMode freq w y) ∧
        |∫ y, F y*continuumLocalizedMode freq v y*continuumLocalizedMode freq w y| ≤
          E*((m:ℝ)+1)/R^32) := by
  obtain ⟨rho,hrho,L,K,hL,hK,D,hD,hfamily⟩ := manufactured_orbital_nuclear_error hp
  refine ⟨rho,hrho,L,K,hL,hK,D,hD,?_⟩
  intro freq hf
  obtain ⟨A,B,C,hA,hB,hC,hgrid⟩ := hfamily freq hf
  let e := 2*((rho:ℝ)*24*(2*Real.pi+1)*64*A*(max 1 (L:ℝ))^4*216)+
    (rho:ℝ)*24*(2*Real.pi+1)*64*A*(max 1 (L:ℝ))^4*13824+
    (rho:ℝ)*2048*Real.pi*B*64*A+C
  refine ⟨max 1 e,le_max_left _ _,?_⟩
  intro R scale S H hR hscale hSlo hShi hH m u hm hsep hcounter hsupp ι _ index hi hcover
  have hR0 : 0 < R := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hS : 1 ≤ S := (one_le_pow₀ hR1).trans hSlo
  obtain ⟨G,hflow,hbij,hLip,hAnti,hfix,hcharge,hreg,hjets,hform⟩ :=
    hgrid scale S hscale hS m u hsep hcounter
  refine ⟨G,hflow,hbij,hLip,hAnti,hfix,hcharge,hreg,hjets,?_⟩
  have hh : 0 < 1/R^10 := by positivity
  have hh1 : 1/R^10 ≤ 1 := (div_le_one (pow_pos hR0 _)).mpr (one_le_pow₀ hR1)
  have hmesh : (m:ℝ)*S*(1/R^10)^2 ≤ 1 := by
    calc
      _ ≤ R^14*(2*R^5)*(1/R^10)^2 := by gcongr
      _ = 2/R := by field_simp [ne_of_gt hR0]
      _ ≤ 1 := (div_le_one hR0).mpr hR
  obtain ⟨hfull,hentries⟩ := hform H hH hsupp index hi (1/R^10) hh hh1 hmesh hcover
  constructor
  · intro n w s i
    have h := hfull n w s i
    have he : D*(1/R^10)^2 = D/R^20 := by field_simp [ne_of_gt hR0]
    rw [he] at h
    exact h
  · intro v w
    obtain ⟨hi,he⟩ := hentries R hR1 v w
    refine ⟨hi,he.trans ?_⟩
    apply (manufactured_orbital_quadrature_physical_scale (Nat.cast_nonneg rho)
      (zero_le_one.trans hA) (zero_le_one.trans hB) (zero_le_one.trans hC) hR1 hShi m).trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right 1 e) (by positivity)) (by positivity)

end ContinuumCoulomb

end

end OAI
