import Mathlib
import OAI.MathematicalPhysics.BFSS.LocalBounds

namespace OAI

/-! Disjoint orbit chambers and smooth cutoff norm exhaustion. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix MeasureTheory Set
variable {N : ℕ} (M : AlgebraData N)
attribute [local irreducible] gaugeAction

lemma gauge_neighborhood_plateau (hN : 2 ≤ N) (q : Boson N)
    (V : Set (Boson N)) (hV : IsOpen V) (hq : q ∈ V)
    (hVi : ∀ U : unitary (ColorMatrix N), ∀ x, M.gaugeAction U x ∈ V ↔ x ∈ V) :
    ∃ (φ : Boson N → ℝ) (W : Set (Boson N)),
      Continuous φ ∧ (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧
      (∀ U : unitary (ColorMatrix N), ∀ x, φ (M.gaugeAction U x) = φ x) ∧
      Function.support φ ⊆ V ∧ IsOpen W ∧ M.gaugeOrbit q ⊆ W ∧
      (∀ x ∈ W, φ x = 1) ∧
      (∀ U : unitary (ColorMatrix N), ∀ x, M.gaugeAction U x ∈ W ↔ x ∈ W) := by
  obtain ⟨a,ha,hab,haq,hai,has⟩ := M.gauge_neighborhood_cutoff hN q V hV hq hVi
  let b : ℝ := 2/(a q)
  have hb : 0 < b := div_pos (by norm_num) haq
  have hbq : b * (a q / 2) = 1 := by dsimp [b]; field_simp
  let φ : Boson N → ℝ := fun x => min 1 (b*a x)
  let W : Set (Boson N) := {x | a q/2 < a x}
  refine ⟨φ,W,continuous_const.min (continuous_const.mul ha),?_,?_,?_,
    isOpen_lt continuous_const ha,?_,?_,?_⟩
  · intro x
    exact ⟨le_min (by norm_num) (mul_nonneg hb.le (hab x).1),min_le_left _ _⟩
  · intro U x
    dsimp [φ]
    rw [hai]
  · intro x hx
    apply has
    intro hz
    apply hx
    simp only [φ,hz,mul_zero,min_eq_right (show (0 : ℝ) ≤ 1 by norm_num)]
  · rintro x ⟨U,hU,rfl⟩
    change a q/2 < a (M.gaugeConjugate U q)
    have he : M.gaugeConjugate U q = M.gaugeAction ⟨U,hU⟩ q := by unfold gaugeAction; rfl
    rw [he]
    rw [hai]
    exact half_lt_self haq
  · intro x hx
    apply min_eq_left
    change a q/2 < a x at hx
    rw [←hbq]
    exact mul_le_mul_of_nonneg_left hx.le hb.le
  · intro U x
    change (a q/2 < a (M.gaugeAction U x)) ↔ (a q/2 < a x)
    rw [hai]
end
end BFSSQuantum.AlgebraData
namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix Set Metric
variable {N : ℕ} (M : AlgebraData N)

lemma gaugeOrbit_image (q : Boson N) (U : unitary (ColorMatrix N)) :
    M.gaugeAction U '' M.gaugeOrbit q = M.gaugeOrbit q := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact M.gaugeOrbit_invariant q x hx U U.prop
  · intro x hx
    refine ⟨M.gaugeAction U⁻¹ x,M.gaugeOrbit_invariant q x hx _ (U⁻¹).prop,?_⟩
    simpa only [inv_inv] using M.gaugeAction_inv U⁻¹ x

lemma gaugeOrbit_infDist (q : Boson N) (U : unitary (ColorMatrix N)) (x : Boson N) :
    infDist (M.gaugeAction U x) (M.gaugeOrbit q) = infDist x (M.gaugeOrbit q) := by
  have hd := Metric.infDist_image (t := M.gaugeOrbit q) (x := x) (M.gaugeIsometry U).isometry
  change infDist (M.gaugeAction U x) (M.gaugeAction U '' M.gaugeOrbit q) = _ at hd
  rwa [M.gaugeOrbit_image] at hd

lemma gaugeOrbit_eq_of_mem (q p : Boson N) (hp : p ∈ M.gaugeOrbit q) :
    M.gaugeOrbit p = M.gaugeOrbit q := by
  obtain ⟨U,hU,rfl⟩ := hp
  have hq : M.gaugeAction ⟨U,hU⟩⁻¹ (M.gaugeConjugate U q) = q :=
    M.gaugeAction_inv ⟨U,hU⟩ q
  apply Set.Subset.antisymm
  · rintro _ ⟨V,hV,rfl⟩
    exact M.gaugeOrbit_invariant q _ ⟨U,hU,rfl⟩ V hV
  · intro x hx
    have hmem : q ∈ M.gaugeOrbit (M.gaugeConjugate U q) :=
      by
        have ht := M.gaugeOrbit_invariant (M.gaugeConjugate U q) _ (M.self_mem_gaugeOrbit _) _ (⟨U,hU⟩⁻¹ : unitary (ColorMatrix N)).prop
        change M.gaugeAction ⟨U,hU⟩⁻¹ (M.gaugeConjugate U q) ∈ _ at ht
        rwa [hq] at ht
    obtain ⟨V,hV,rfl⟩ := hx
    exact M.gaugeOrbit_invariant _ q hmem V hV

lemma gaugeOrbit_disjoint_of_ne (q p : Boson N) (hqp : M.gaugeOrbit q ≠ M.gaugeOrbit p) :
    Disjoint (M.gaugeOrbit q) (M.gaugeOrbit p) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hqp ((M.gaugeOrbit_eq_of_mem q x hx).symm.trans (M.gaugeOrbit_eq_of_mem p x hy))

theorem massiveZeros_disjoint_orbits (hN : 2 ≤ N) :
    ∃ S : Set (Boson N), S.Finite ∧ S ⊆ M.massiveZeros ∧
      M.massiveZeros = ⋃ q ∈ S, M.gaugeOrbit q ∧
      S.PairwiseDisjoint M.gaugeOrbit := by
  obtain ⟨S,hSf,hS,hcov⟩ := M.massiveZeros_finite_orbits hN
  obtain ⟨T,hTS,hinj,himage⟩ := (Set.surjOn_image M.gaugeOrbit S).exists_subset_injOn_image_eq
  refine ⟨T,hSf.subset hTS,hTS.trans hS,?_,?_⟩
  · apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨q,hq,hxq⟩ := Set.mem_iUnion₂.mp (hcov ▸ hx)
      obtain ⟨p,hp,he⟩ := (himage ▸ (show M.gaugeOrbit q ∈ M.gaugeOrbit '' S from ⟨q,hq,rfl⟩))
      exact Set.mem_iUnion₂.mpr ⟨p,hp,he.symm ▸ hxq⟩
    · intro x hx
      obtain ⟨q,hq,hxq⟩ := Set.mem_iUnion₂.mp hx
      exact M.gaugeOrbit_subset_massiveZeros q (hS (hTS hq)) hxq
  · intro q hq p hp hqp
    apply M.gaugeOrbit_disjoint_of_ne
    exact fun he => hqp (hinj hq hp he)

def orbitChamber {ι : Type*} (q : ι → Boson N) (i : ι) : Set (Boson N) :=
  {x | ∀ j, i ≠ j → infDist x (M.gaugeOrbit (q i)) < infDist x (M.gaugeOrbit (q j))}

lemma orbitChamber_open {ι : Type*} [Finite ι] (q : ι → Boson N) (i : ι) :
    IsOpen (M.orbitChamber q i) := by
  classical
  unfold orbitChamber
  simp only [ofPred_forall]
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro hij
  exact isOpen_lt (continuous_infDist_pt _) (continuous_infDist_pt _)

lemma orbitChamber_gauge {ι : Type*} (q : ι → Boson N) (i : ι)
    (U : unitary (ColorMatrix N)) (x : Boson N) :
    M.gaugeAction U x ∈ M.orbitChamber q i ↔ x ∈ M.orbitChamber q i := by
  simp only [orbitChamber,mem_ofPred_eq,M.gaugeOrbit_infDist]

lemma orbitChamber_contains {ι : Type*} (q : ι → Boson N) (hN : 2 ≤ N)
    (hdis : Pairwise (fun i j => Disjoint (M.gaugeOrbit (q i)) (M.gaugeOrbit (q j)))) (i : ι) :
    M.gaugeOrbit (q i) ⊆ M.orbitChamber q i := by
  intro x hx j hij
  have hn : x ∉ M.gaugeOrbit (q j) := fun hj => Set.disjoint_left.mp (hdis hij) hx hj
  rw [infDist_zero_of_mem hx]
  exact ((M.gaugeOrbit_isCompact hN (q j)).isClosed.notMem_iff_infDist_pos
    ⟨q j,M.self_mem_gaugeOrbit (q j)⟩).mp hn

lemma orbitChamber_disjoint {ι : Type*} (q : ι → Boson N) :
    Pairwise (fun i j => Disjoint (M.orbitChamber q i) (M.orbitChamber q j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  exact (hi j hij).not_gt (hj i hij.symm)
end
end BFSSQuantum.AlgebraData
namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix MeasureTheory Set Metric
variable {N : ℕ} (M : AlgebraData N)
attribute [local irreducible] massiveDistance coreToL2

theorem massive_core_cutoff_exhaustion (hN : 2 ≤ N)
    (W : Set (Boson N)) (hW : IsOpen W) (hZW : M.massiveZeros ⊆ W) :
    ∃ δ c K : ℝ, 0 < δ ∧ 0 < c ∧ 0 ≤ K ∧
      ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ χ : Boson N → ℝ,
        Continuous χ → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
        (∀ x ∈ W, χ x = 1) → ∀ f : SmoothCore N,
        0 ≤ ‖coreToL2 f‖^2 - (∫ x, χ (h • x)*‖f x‖^2) ∧
        c/2*δ^2*(‖coreToL2 f‖^2 - (∫ x, χ (h • x)*‖f x‖^2)) ≤
          h^2*(M.deformedCoreEnergy h 1 f + K*‖coreToL2 f‖^2) := by
  obtain ⟨δ,hδ,hδW⟩ := (M.massiveZeros_isCompact hN).exists_thickening_subset_open hW hZW
  obtain ⟨c,K,hc,hK,hform⟩ := M.massive_core_uniform_distance hN
  refine ⟨δ,c,K,hδ,hc,hK,?_⟩
  intro h hh h1 χ hχ hχb hχW f
  have hsmul : Continuous (fun x : Boson N => h • x) :=
    (continuous_const : Continuous (fun _ : Boson N => h)).smul continuous_id
  have hχi : Integrable (fun x => χ (h • x)*‖f x‖^2) :=
    weighted_core_square_integrable _ (hχ.comp hsmul) f
  have hrem : Integrable (fun x => (1 - χ (h • x))*‖f x‖^2) :=
    weighted_core_square_integrable _ (continuous_const.sub (hχ.comp hsmul)) f
  have he : ‖coreToL2 f‖^2 - (∫ x, χ (h • x)*‖f x‖^2) =
      ∫ x, (1 - χ (h • x))*‖f x‖^2 := by
    rw [coreToL2_norm_sq,←integral_sub (coreNormSq_integrable f) hχi]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [he]
  refine ⟨integral_nonneg (fun _ => mul_nonneg (sub_nonneg.mpr (hχb _).2) (sq_nonneg _)),?_⟩
  have hpoint (x : Boson N) : δ^2*(1-χ (h • x)) ≤ h^2*(M.massiveDistance h x)^2 := by
    by_cases hx : h • x ∈ W
    · rw [hχW _ hx,sub_self,mul_zero]
      positivity
    · have hd : δ ≤ infDist (h • x) M.massiveZeros := by
        apply le_of_not_gt
        intro hd
        exact hx (hδW ((mem_thickening_iff_infDist_lt ⟨0,M.zero_mem_massiveZeros⟩).mpr hd))
      have hd2 : δ^2 ≤ (infDist (h • x) M.massiveZeros)^2 :=
        pow_le_pow_left₀ hδ.le hd 2
      rw [M.massiveDistance_rescale h hh,mul_pow] at hd2
      exact (mul_le_of_le_one_right (sq_nonneg _) (sub_le_self _ (hχb _).1)).trans hd2
  have hi : δ^2 * (∫ x, (1 - χ (h • x))*‖f x‖^2) ≤
      h^2 * (∫ x, (M.massiveDistance h x)^2*‖f x‖^2) := by
    rw [←integral_const_mul,←integral_const_mul]
    apply integral_mono (hrem.const_mul _) ((weighted_core_square_integrable _
      ((M.massiveDistance_continuous h).pow 2) f).const_mul _)
    intro x
    change δ^2*((1-χ (h • x))*‖f x‖^2) ≤ h^2*((M.massiveDistance h x)^2*‖f x‖^2)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hpoint x) (sq_nonneg ‖f x‖)
  have hf := hform h hh h1 f
  have hgrad : 0 ≤ (1/2:ℝ) * ∑ p : SpaceIndex × ColorIndex N,
      ‖coreToL2 (coordinateDerivative p.1 p.2 f)‖^2 :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hb := mul_le_mul_of_nonneg_left (le_of_add_le_of_nonneg_right hf hgrad) (sq_nonneg h)
  have hi' := mul_le_mul_of_nonneg_left hi (show 0 ≤ c/2 by positivity)
  calc
    _ = c/2*(δ^2*(∫ x, (1 - χ (h • x))*‖f x‖^2)) := by ring
    _ ≤ c/2*(h^2*(∫ x, (M.massiveDistance h x)^2*‖f x‖^2)) := hi'
    _ = h^2*(c/2*(∫ x, (M.massiveDistance h x)^2*‖f x‖^2)) := by ring
    _ ≤ _ := hb
end
end BFSSQuantum.AlgebraData

end OAI
