import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedNuclearForm
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedTransport

namespace OAI

/-! One fixed integer background density and one fixed constant suffice
for the general nuclear replacement form estimate over the whole family. -/

noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace ContinuumCoulomb

theorem manufactured_uniform_nuclear_form (hpublished : PublishedC4FlowInput) :
    ∃ rho : ℕ, 0 < rho ∧ ∃ L K : ℝ≥0, 0 < L ∧ 0 < K ∧ ∃ B : ℝ, 1 ≤ B ∧
    ∀ (freq scale S : ℝ), 0 < scale → 1 ≤ S →
      ∀ (m : ℕ) (u : Fin m → PlanarPosition),
      (∀ i j, i ≠ j → 3 ≤ ‖u i-u j‖) →
      (∀ i, localizedCounterterm freq u i ≤ scale) →
      ∃ G : Position → ℝ → Position,
        IsUnitTimeFlow (moserVelocity rho (manufacturedWellField freq scale S u)) G ∧
        Function.Bijective (fun x => G x 1) ∧
        LipschitzWith L (fun x => G x 1) ∧ AntilipschitzWith K (fun x => G x 1) ∧
        (∀ x, x ∉ tsupport (manufacturedWellField freq scale S u) → G x 1 = x) ∧
      ∀ (H : ℝ), 0 ≤ H → tsupport (manufacturedWellField freq scale S u) ⊆ slabDomain H S →
      ∀ {ι : Type} [Fintype ι] (index : ι → Fin 3 → ℤ), Function.Injective index →
      ∀ (h : ℝ), 0 < h → h ≤ 1 → (m:ℝ)*S*h^2 ≤ 1 →
      (⋃ i, positionCube (gaussCellCenter h (index i)) h) = slabDomain H S →
      ∀ (n : ℕ) (w : Coulomb.H1Vector n) (s : SpinConfiguration n) (i : Fin n),
      |∫ x, (gridNuclearPotential index (fun x => G x 1) rho h (Coulomb.position x i)-
        (slabPotential rho H S (Coulomb.position x i)+
          manufacturedWellField freq scale S u (Coulomb.position x i)))*‖w.value s x‖^2| ≤
      B*h^2*((∫ x, ‖w.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖w.gradient s (i,k) x‖^2) := by
  obtain ⟨rho,hrho,L,K,hL,hK,hfamily⟩ := manufactured_transport_family_with_charge hpublished
  obtain ⟨C,A,hC,hA,hform⟩ := manufactured_grid_form_error hpublished L K hL hK
  let D : ℝ := max 1 (L:ℝ)
  let E : ℝ := (rho:ℝ)*(24*C*D^4*(3072*Real.pi/(L:ℝ)^2+216)+108*Real.pi*(L:ℝ)^2)
  let B : ℝ := max 1 (E+(rho:ℝ)*A)
  have hD : 1 ≤ D := le_max_left _ _
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hrhoR : (0:ℝ) < rho := by exact_mod_cast hrho
  refine ⟨rho,hrho,L,K,hL,hK,B,le_max_left _ _,?_⟩
  intro freq scale S hscale hS m u hsep hcounter
  obtain ⟨hcharge,G,hflow,hbij,hLip,hAnti,hfix,_hreg,hjets⟩ :=
    hfamily freq scale S hscale hS m u hsep hcounter
  refine ⟨G,hflow,hbij,hLip,hAnti,hfix,?_⟩
  intro H hH hsupp ι _ index hindex h hh hh1 hmesh hcover n w s i
  have hGD (x : Position) (k : ℕ) (hk : 1 ≤ k) (hk4 : k ≤ 4) :
      ‖iteratedFDeriv ℝ k (fun x => G x 1) x‖ ≤ D^k := by
    apply (hjets k hk hk4 x).trans
    exact (le_max_right 1 (L:ℝ)).trans (by simpa only [pow_one] using pow_le_pow_right₀ hD hk)
  have he := hform rho H S freq scale m u hrhoR hH hS hcharge hsupp G hflow hbij hfix D hD hGD
    hLip hAnti index hindex h hh hh1 hcover n w s i
  have hmass : 0 ≤ ∫ x, ‖w.value s x‖^2 := integral_nonneg (fun _ => sq_nonneg _)
  have hgrad : 0 ≤ ∑ k : Fin 3, ∫ x, ‖w.gradient s (i,k) x‖^2 :=
    Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  have hsize : (m:ℝ)*S*h^4 ≤ h^2 := by
    calc
      _ = h^2*((m:ℝ)*S*h^2) := by ring
      _ ≤ h^2*1 := mul_le_mul_of_nonneg_left hmesh (sq_nonneg h)
      _ = _ := mul_one _
  have hb : (rho:ℝ)*(24*C*D^4*(3072*Real.pi*h^2/(L:ℝ)^2+216*m*S*h^4)+
      108*Real.pi*(L:ℝ)^2*h^2) ≤ E*h^2 := by
    have hs := mul_le_mul_of_nonneg_left hsize (by norm_num : (0:ℝ) ≤ 216)
    have ht := mul_le_mul_of_nonneg_left
      (add_le_add_left hs (3072*Real.pi*h^2/(L:ℝ)^2)) (by positivity : 0 ≤ 24*C*D^4)
    have ht' := mul_le_mul_of_nonneg_left
      (add_le_add_right ht (108*Real.pi*(L:ℝ)^2*h^2)) hrhoR.le
    dsimp only [E]
    convert ht' using 1 <;> ring
  apply he.trans
  calc
    _ ≤ E*h^2*(∫ x, ‖w.value s x‖^2)+(rho:ℝ)*A*h^2*
        ((∫ x, ‖w.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖w.gradient s (i,k) x‖^2) :=
      add_le_add (mul_le_mul_of_nonneg_right hb hmass) le_rfl
    _ ≤ (E+(rho:ℝ)*A)*h^2*
        ((∫ x, ‖w.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖w.gradient s (i,k) x‖^2) := by
      nlinarith [mul_nonneg (mul_nonneg hE (sq_nonneg h)) hgrad]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show E+(rho:ℝ)*A ≤ B from le_max_right _ _) (sq_nonneg h))
      (add_nonneg hmass hgrad)

end ContinuumCoulomb

end

end OAI
