import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.UniformAbsoluteNuclearForm
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CompactOrbitalNuclearError
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.OrbitalNuclearTail

namespace OAI

/-! Actual uncut orbital matrix elements of the manufactured grid potential.
The only external analytic input is the published C4 flow theorem. -/

noncomputable section
open MeasureTheory
open scoped NNReal
namespace ContinuumCoulomb

theorem manufactured_orbital_nuclear_error (hpublished : PublishedC4FlowInput) :
    ∃ rho : ℕ, 0 < rho ∧ ∃ L K : ℝ≥0, 0 < L ∧ 0 < K ∧ ∃ D : ℝ, 1 ≤ D ∧
    ∀ freq : ℝ, 0 < freq → ∃ A B C : ℝ, 1 ≤ A ∧ 1 ≤ B ∧ 1 ≤ C ∧
    ∀ (scale S : ℝ), 0 < scale → 1 ≤ S →
    ∀ (m : ℕ) (u : Fin m → PlanarPosition),
    (∀ i j, i ≠ j → 3 ≤ ‖u i-u j‖) →
    (∀ i, localizedCounterterm freq u i ≤ scale) →
    ∃ G : Position → ℝ → Position,
      IsUnitTimeFlow (moserVelocity rho (manufacturedWellField freq scale S u)) G ∧
      Function.Bijective (fun x => G x 1) ∧
      LipschitzWith L (fun x => G x 1) ∧ AntilipschitzWith K (fun x => G x 1) ∧
      (∀ x, x ∉ tsupport (manufacturedWellField freq scale S u) → G x 1 = x) ∧
      (∀ x, |manufacturedCharge (manufacturedWellField freq scale S u) x| ≤ (rho:ℝ)/2) ∧
      ContDiff ℝ 4 (fun x => G x 1) ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k (fun y => G y 1) x‖ ≤ L) ∧
    ∀ H : ℝ, 0 ≤ H → tsupport (manufacturedWellField freq scale S u) ⊆ slabDomain H S →
    ∀ {ι : Type} [Fintype ι] (index : ι → Fin 3 → ℤ), Function.Injective index →
    ∀ h : ℝ, 0 < h → h ≤ 1 → (m:ℝ)*S*h^2 ≤ 1 →
    (⋃ i, positionCube (gaussCellCenter h (index i)) h) = slabDomain H S →
      (∀ (n : ℕ) (w : Coulomb.H1Vector n) (s : SpinConfiguration n) (i : Fin n),
        Integrable (fun x => |gridNuclearPotential index (fun x => G x 1) rho h (Coulomb.position x i)-
          (slabPotential rho H S (Coulomb.position x i)+
            manufacturedWellField freq scale S u (Coulomb.position x i))| * ‖w.value s x‖^2) ∧
        (∫ x, |gridNuclearPotential index (fun x => G x 1) rho h (Coulomb.position x i)-
          (slabPotential rho H S (Coulomb.position x i)+
            manufacturedWellField freq scale S u (Coulomb.position x i))| * ‖w.value s x‖^2) ≤
        D*h^2*((∫ x, ‖w.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖w.gradient s (i,k) x‖^2)) ∧
    ∀ R : ℝ, 1 ≤ R → ∀ v w : PlanarPosition,
      Integrable (fun y => (gridNuclearPotential index (fun x => G x 1) rho h y-
        (slabPotential rho H S y+manufacturedWellField freq scale S u y))*
        continuumLocalizedMode freq v y*continuumLocalizedMode freq w y) ∧
      |∫ y, (gridNuclearPotential index (fun x => G x 1) rho h y-
        (slabPotential rho H S y+manufacturedWellField freq scale S u y))*
        continuumLocalizedMode freq v y*continuumLocalizedMode freq w y| ≤
      rho*(24*((2*Real.pi+1)*(64*A*R^3))*(max 1 (L:ℝ))^4*(216*m*S+13824*R^3)+
        2048*Real.pi*B*(64*A*R^3))*h^4+C*h^2/R^12 := by
  obtain ⟨rho,hrho,L,K,hL,hK,D,hD,hfamily⟩ := manufactured_uniform_nuclear_absolute_form hpublished
  refine ⟨rho,hrho,L,K,hL,hK,D,hD,?_⟩
  intro freq hfreq
  obtain ⟨A,B,hA,hB,hcompact⟩ := manufactured_compact_orbital_nuclear_error hpublished hfreq
  obtain ⟨T,hT,htail⟩ := orbital_nuclear_cutoff_error hfreq
  let C := max 1 (T*D)
  have hC : 1 ≤ C := le_max_left _ _
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hrhoR : (0:ℝ) < rho := by exact_mod_cast hrho
  refine ⟨A,B,C,hA,hB,hC,?_⟩
  intro scale S hscale hS m u hsep hcounter
  obtain ⟨G,hflow,hbij,hLip,hAnti,hfix,hcharge,hreg,hjets,hform⟩ :=
    hfamily freq scale S hscale hS m u hsep hcounter
  refine ⟨G,hflow,hbij,hLip,hAnti,hfix,hcharge,hreg,hjets,?_⟩
  intro H hH hsupp ι _ index hindex h hh hh1 hmesh hcover
  have hfull := hform H hH hsupp index hindex h hh hh1 hmesh hcover
  refine ⟨hfull,?_⟩
  intro R hR v w
  let F : Position → ℝ := fun y => gridNuclearPotential index (fun x => G x 1) rho h y-
    (slabPotential rho H S y+manufacturedWellField freq scale S u y)
  have hF : Measurable F := (gridNuclearPotential_measurable index (fun x => G x 1) rho h).sub
    (((slabPotential_continuous hrhoR.le hH (zero_le_one.trans hS)).add
      (manufacturedWellField_C7 freq scale S u).continuous).measurable)
  obtain ⟨hi,hic,he⟩ := htail (D*h^2) R (mul_nonneg hD0 (sq_nonneg h)) hR F hF
    (fun w s => (hfull 1 w s 0).1) (fun w s => (hfull 1 w s 0).2) v w
  refine ⟨hi,?_⟩
  have hmax : 1 ≤ max 1 (L:ℝ) := le_max_left _ _
  have hjet (x : Position) (k : ℕ) (hk : 1 ≤ k) (hk4 : k ≤ 4) :
      ‖iteratedFDeriv ℝ k (fun x => G x 1) x‖ ≤ (max 1 (L:ℝ))^k :=
    (hjets k hk hk4 x).trans ((le_max_right 1 (L:ℝ)).trans
      (by simpa only [pow_one] using pow_le_pow_right₀ hmax hk))
  have hc := hcompact R hR v w rho H S scale hrhoR hH hS m u hcharge hsupp
    G hflow hbij hreg hfix (max 1 (L:ℝ)) (zero_le_one.trans hmax) hjet
    index hindex h hh hh1 hcover
  have htriangle := abs_add_le
    ((∫ y, F y*continuumLocalizedMode freq v y*continuumLocalizedMode freq w y)-
      ∫ y, F y*compactOrbitalDensity freq R v w y)
    (∫ y, F y*compactOrbitalDensity freq R v w y)
  rw [sub_add_cancel] at htriangle
  have htailC : T*(D*h^2)/R^12 ≤ C*h^2/R^12 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (le_max_right 1 (T*D)) (sq_nonneg h)
  exact htriangle.trans ((add_le_add (he.trans htailC) hc).trans_eq (add_comm _ _))

end ContinuumCoulomb

end

end OAI
