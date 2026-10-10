import OAI.Analysis.Triangular.Energy.Basic

namespace OAI

noncomputable section
open scoped BigOperators Topology ENNReal NNReal
open Classical Filter
namespace TriangularUniversal
def b : ℝ := Real.sqrt 3 / 2

def nodeResidues : Finset ℕ := {0, 1, 3, 4, 7, 9}

def IsPositiveNode (s : ℝ) : Prop :=
  0 < s ∧ ∃ q : ℤ, ∃ a ∈ nodeResidues, s = 12 * (q : ℝ) + a

lemma sqrt_three_pos : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
lemma scale_pos : 0 < Real.sqrt (2 / Real.sqrt (3 : ℝ)) := by positivity
lemma b_pos : 0 < b := by unfold b; positivity

lemma triangularPoint_coord_zero (j k : ℤ) :
    triangularPoint (j, k) 0 = Real.sqrt (2 / Real.sqrt 3) * ((j : ℝ) + (k : ℝ) / 2) := by
  simp [triangularPoint]

lemma triangularPoint_coord_one (j k : ℤ) :
    triangularPoint (j, k) 1 = Real.sqrt (2 / Real.sqrt 3) * ((k : ℝ) * Real.sqrt 3 / 2) := by
  simp [triangularPoint]

lemma triangularPoint_norm_sq (j k : ℤ) :
    b * ‖triangularPoint (j, k)‖ ^ 2 = (j : ℝ) ^ 2 + (j : ℝ) * (k : ℝ) + (k : ℝ) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp only [triangularPoint_coord_zero, triangularPoint_coord_one, Real.norm_eq_abs,
    sq_abs, mul_pow]
  have hs : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hc : (Real.sqrt (2 / Real.sqrt (3 : ℝ))) ^ 2 = 2 / Real.sqrt 3 :=
    Real.sq_sqrt (by positivity)
  rw [hc]
  dsimp [b]
  field_simp
  nlinarith [hs]

lemma triangularPoint_injective : Function.Injective triangularPoint := by
  intro jk lm he
  rcases jk with ⟨j, k⟩
  rcases lm with ⟨l, m⟩
  have hzero := congrArg (fun v : Plane => v 0) he
  have hone := congrArg (fun v : Plane => v 1) he
  simp only [triangularPoint_coord_zero, triangularPoint_coord_one] at hzero hone
  have hk : k = m := by
    have hr : (k : ℝ) = (m : ℝ) := by
      have H := (mul_left_cancel₀ (ne_of_gt scale_pos)) hone
      have H' : (k : ℝ) * Real.sqrt 3 = (m : ℝ) * Real.sqrt 3 := by linarith
      exact mul_right_cancel₀ (ne_of_gt sqrt_three_pos) H' 
    exact_mod_cast hr
  subst m
  have hj : j = l := by
    have hr : (j : ℝ) = (l : ℝ) := by
      have H := (mul_left_cancel₀ (ne_of_gt scale_pos)) hzero
      linarith
    exact_mod_cast hr
  subst l
  rfl

lemma triangularPoint_zero : triangularPoint (0, 0) = 0 := by
  ext i
  fin_cases i <;> simp [triangularPoint]

lemma triangularPoint_sub (j k : ℤ × ℤ) :
    triangularPoint (j - k) = triangularPoint j - triangularPoint k := by
  ext i
  fin_cases i <;> simp [triangularPoint] <;> ring

lemma eisenstein_mod_twelve : ∀ j k : ZMod 12,
    j ^ 2 + j * k + k ^ 2 = 0 ∨ j ^ 2 + j * k + k ^ 2 = 1 ∨
    j ^ 2 + j * k + k ^ 2 = 3 ∨ j ^ 2 + j * k + k ^ 2 = 4 ∨
    j ^ 2 + j * k + k ^ 2 = 7 ∨ j ^ 2 + j * k + k ^ 2 = 9 := by decide

lemma eisenstein_mod_twelve_int (j k : ℤ) :
    (j ^ 2 + j * k + k ^ 2) % 12 = 0 ∨
    (j ^ 2 + j * k + k ^ 2) % 12 = 1 ∨
    (j ^ 2 + j * k + k ^ 2) % 12 = 3 ∨
    (j ^ 2 + j * k + k ^ 2) % 12 = 4 ∨
    (j ^ 2 + j * k + k ^ 2) % 12 = 7 ∨
    (j ^ 2 + j * k + k ^ 2) % 12 = 9 := by
  have H := eisenstein_mod_twelve (j : ZMod 12) (k : ZMod 12)
  have hm (r : ℤ) (hr : (j : ZMod 12)^2 + (j : ZMod 12)*k + (k : ZMod 12)^2 = r) :
      (j ^ 2 + j * k + k ^ 2) % 12 = r % 12 := by
    apply (ZMod.intCast_eq_intCast_iff' _ _ 12).mp
    push_cast
    exact hr
  rcases H with H | H | H | H | H | H
  · exact Or.inl (by simpa using hm 0 H)
  · exact Or.inr (Or.inl (by simpa using hm 1 H))
  · exact Or.inr (Or.inr (Or.inl (by simpa using hm 3 H)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa using hm 4 H))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simpa using hm 7 H)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simpa using hm 9 H)))))

lemma triangular_shell_node (a : Plane) (ha : a ∈ triangularLattice) (ha0 : a ≠ 0) :
    IsPositiveNode (b * ‖a‖ ^ 2) := by
  rcases ha with ⟨⟨j, k⟩, rfl⟩
  have hpos : 0 < b * ‖triangularPoint (j, k)‖ ^ 2 :=
    mul_pos b_pos (sq_pos_of_pos (norm_pos_iff.mpr ha0))
  refine ⟨hpos, ?_⟩
  rw [triangularPoint_norm_sq]
  let n : ℤ := j ^ 2 + j * k + k ^ 2
  have hn : (j : ℝ) ^ 2 + (j : ℝ) * (k : ℝ) + (k : ℝ) ^ 2 = (n : ℝ) := by
    dsimp [n]; push_cast; ring
  rw [hn]
  have he := Int.emod_add_mul_ediv n 12
  refine ⟨n / 12, ?_⟩
  have H := eisenstein_mod_twelve_int j k
  change n % 12 = 0 ∨ n % 12 = 1 ∨ n % 12 = 3 ∨ n % 12 = 4 ∨
    n % 12 = 7 ∨ n % 12 = 9 at H
  rcases H with H | H | H | H | H | H
  all_goals rw [H] at he
  · refine ⟨0, by simp [nodeResidues], ?_⟩
    exact_mod_cast (by linarith [he] : n = 12 * (n / 12) + _)
  · refine ⟨1, by simp [nodeResidues], ?_⟩
    exact_mod_cast (by linarith [he] : n = 12 * (n / 12) + _)
  · refine ⟨3, by simp [nodeResidues], ?_⟩
    exact_mod_cast (by linarith [he] : n = 12 * (n / 12) + _)
  · refine ⟨4, by simp [nodeResidues], ?_⟩
    exact_mod_cast (by linarith [he] : n = 12 * (n / 12) + _)
  · refine ⟨7, by simp [nodeResidues], ?_⟩
    exact_mod_cast (by linarith [he] : n = 12 * (n / 12) + _)
  · refine ⟨9, by simp [nodeResidues], ?_⟩
    exact_mod_cast (by linarith [he] : n = 12 * (n / 12) + _)

lemma triangularLattice_sub {x y : Plane} (hx : x ∈ triangularLattice)
    (hy : y ∈ triangularLattice) : x - y ∈ triangularLattice := by
  rcases hx with ⟨j, rfl⟩
  rcases hy with ⟨k, rfl⟩
  exact ⟨j - k, triangularPoint_sub j k⟩

lemma diskPoints_subset (C : Set Plane) (R : ℝ) :
    (diskPoints C R : Set Plane) ⊆ C := by
  intro x hx
  unfold diskPoints at hx
  split_ifs at hx with h
  · exact (h.mem_toFinset.mp hx).1
  · simp at hx

lemma finite_lattice_row_le (g : ℝ → ℝ) (s : Finset Plane)
    (hs : (s : Set Plane) ⊆ triangularLattice) (x : Plane)
    (hx : x ∈ triangularLattice) :
    ∑ y ∈ s.erase x, ENNReal.ofReal (g (‖x - y‖ ^ 2)) ≤ latticeEnergy g := by
  let f : {y : Plane // y ∈ s.erase x} →
      {a : Plane // a ∈ triangularLattice ∧ a ≠ 0} :=
    fun y => ⟨x - y.val, triangularLattice_sub hx (hs (Finset.mem_of_mem_erase y.property)),
      sub_ne_zero.mpr (Ne.symm (Finset.ne_of_mem_erase y.property))⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    have H := congrArg Subtype.val h
    dsimp [f] at H
    exact sub_right_injective H
  have H := ENNReal.tsum_comp_le_tsum_of_injective hf
    (fun a : {a : Plane // a ∈ triangularLattice ∧ a ≠ 0} =>
      ENNReal.ofReal (g (‖a.val‖ ^ 2)))
  change (∑' y : (s.erase x), ENNReal.ofReal (g (‖x - (y : Plane)‖ ^ 2))) ≤
    latticeEnergy g at H
  rw [tsum_fintype] at H
  have he := Finset.sum_subtype (F := inferInstance) (s.erase x) (fun _ => Iff.rfl)
    (fun y : Plane => ENNReal.ofReal (g (‖x - y‖ ^ 2)))
  exact he ▸ H

lemma lattice_disk_energy_le (g : ℝ → ℝ) (R : ℝ) :
    diskEnergy g triangularLattice R ≤ latticeEnergy g := by
  let s := diskPoints triangularLattice R
  have hs : (s : Set Plane) ⊆ triangularLattice := diskPoints_subset _ _
  by_cases hn : s.card = 0
  · have he : s = ∅ := Finset.card_eq_zero.mp hn
    change (s.card : ℝ≥0∞)⁻¹ * (∑ x ∈ s, ∑ y ∈ s.erase x,
      ENNReal.ofReal (g (‖x - y‖ ^ 2))) ≤ _
    simp [he]
  have hn' : (s.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn
  have H : (∑ x ∈ s, ∑ y ∈ s.erase x, ENNReal.ofReal (g (‖x - y‖ ^ 2))) ≤
      (s.card : ℝ≥0∞) * latticeEnergy g := by
    calc
      _ ≤ ∑ x ∈ s, latticeEnergy g := Finset.sum_le_sum fun x hx =>
        finite_lattice_row_le g s hs x (hs hx)
      _ = _ := by simp
  change (s.card : ℝ≥0∞)⁻¹ * _ ≤ _
  calc
    _ ≤ (s.card : ℝ≥0∞)⁻¹ * ((s.card : ℝ≥0∞) * latticeEnergy g) :=
      mul_le_mul_of_nonneg_left H zero_le
    _ = latticeEnergy g := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hn' (by simp), one_mul]

lemma lattice_energy_upper (g : ℝ → ℝ) :
    energy g triangularLattice ≤ latticeEnergy g := by
  apply Filter.liminf_le_of_frequently_le'
  exact Filter.Eventually.frequently (Filter.Eventually.of_forall (lattice_disk_energy_le g))

def triangularEquiv : (Fin 2 → ℝ) ≃ₗ[ℝ] Plane where
  toFun v := Real.sqrt (2 / Real.sqrt 3) •
    (EuclideanSpace.single 0 (v 0 + v 1 / 2) +
      EuclideanSpace.single 1 (v 1 * Real.sqrt 3 / 2))
  invFun v := ![v 0 / Real.sqrt (2 / Real.sqrt 3) -
    v 1 / (Real.sqrt (2 / Real.sqrt 3) * Real.sqrt 3),
    2 * v 1 / (Real.sqrt (2 / Real.sqrt 3) * Real.sqrt 3)]
  left_inv v := by
    ext i
    fin_cases i <;> simp
    all_goals field_simp [ne_of_gt scale_pos, ne_of_gt sqrt_three_pos] <;> ring
  right_inv v := by
    ext i
    fin_cases i <;> simp
    all_goals field_simp [ne_of_gt scale_pos, ne_of_gt sqrt_three_pos] <;> ring
  map_add' u v := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c v := by
    ext i
    fin_cases i <;> simp <;> ring

def triangularBasis : Module.Basis (Fin 2) ℝ Plane :=
  Module.Basis.ofEquivFun triangularEquiv.symm

def triangularModule : Submodule ℤ Plane :=
  Submodule.span ℤ (Set.range triangularBasis)

lemma triangularPoint_equiv (j k : ℤ) :
    triangularPoint (j, k) = triangularEquiv ![(j : ℝ), (k : ℝ)] := rfl

lemma triangularModule_coe : (triangularModule : Set Plane) = triangularLattice := by
  ext x
  change x ∈ Submodule.span ℤ (Set.range triangularBasis) ↔ _
  rw [triangularBasis.mem_span_iff_repr_mem ℤ x]
  constructor
  · intro h
    rcases h 0 with ⟨j, hj⟩
    rcases h 1 with ⟨k, hk⟩
    refine ⟨(j, k), ?_⟩
    apply triangularEquiv.symm.injective
    rw [triangularPoint_equiv, LinearEquiv.symm_apply_apply]
    ext i
    fin_cases i
    · exact hj
    · exact hk
  · rintro ⟨⟨j, k⟩, rfl⟩ i
    fin_cases i
    · refine ⟨j, ?_⟩
      change (j : ℝ) = (triangularEquiv.symm (triangularPoint (j, k))) 0
      rw [triangularPoint_equiv, LinearEquiv.symm_apply_apply]
      rfl
    · refine ⟨k, ?_⟩
      change (k : ℝ) = (triangularEquiv.symm (triangularPoint (j, k))) 1
      rw [triangularPoint_equiv, LinearEquiv.symm_apply_apply]
      rfl

instance : DiscreteTopology triangularModule :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range triangularBasis)))

instance : IsZLattice ℝ triangularModule :=
  inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ (Set.range triangularBasis)))

lemma triangular_locallyFinite : LocallyFinite triangularLattice := by
  intro R
  rw [← triangularModule_coe, Set.inter_comm]
  exact ZSpan.setFinite_inter triangularBasis Metric.isBounded_closedBall

lemma triangularBasis_apply (i : Fin 2) :
    triangularBasis i = triangularEquiv (Pi.single i 1) := by
  simp [triangularBasis, Module.Basis.coe_ofEquivFun]

lemma triangular_det :
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.det triangularBasis = 1 := by
  rw [Module.Basis.det_apply, Matrix.det_fin_two]
  simp only [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr, triangularBasis_apply]
  simp only [triangularEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  have hs := Real.sq_sqrt (le_of_lt (show 0 < 2 / Real.sqrt 3 from div_pos (by norm_num) sqrt_three_pos))
  generalize Real.sqrt (2 / Real.sqrt 3) = a at hs ⊢
  simp
  field_simp [ne_of_gt sqrt_three_pos] at hs ⊢
  nlinarith

lemma triangular_covolume : ZLattice.covolume triangularModule = 1 := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain triangularModule
    MeasureTheory.volume (ZSpan.isAddFundamentalDomain triangularBasis MeasureTheory.volume)]
  rw [ZSpan.measureReal_fundamentalDomain triangularBasis MeasureTheory.volume
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis, triangular_det, abs_one, one_mul]
  rw [MeasureTheory.measureReal_def, MeasureTheory.measure_congr
    (ZSpan.fundamentalDomain_ae_parallelepiped
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis MeasureTheory.volume)]
  change (MeasureTheory.volume (parallelepiped (EuclideanSpace.basisFun (Fin 2) ℝ))).toReal = 1
  rw [OrthonormalBasis.volume_parallelepiped, ENNReal.toReal_one]

lemma diskCount_eq_card (C : Set Plane) (hC : LocallyFinite C) (R : ℝ) :
    diskCount C R = Nat.card (C ∩ Metric.closedBall (0 : Plane) R : Set Plane) := by
  unfold diskCount diskPoints
  rw [dite_eq_left (hC R)]
  exact (Set.ncard_eq_toFinset_card _ (hC R)).symm

lemma norm_square_sublevel (R : ℝ) (hR : 0 ≤ R) :
    {x : Plane | x ∈ (Set.univ : Set Plane) ∧ ‖x‖ ^ 2 ≤ R ^ 2} =
      Metric.closedBall (0 : Plane) R := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_univ, true_and, Metric.mem_closedBall, dist_zero_right]
  constructor <;> intro h <;> nlinarith [norm_nonneg x]

lemma triangular_count_asymptotic :
    Tendsto (fun R : ℝ => (diskCount triangularLattice R : ℝ) / R ^ 2)
      atTop (𝓝 Real.pi) := by
  have hunit : {x : Plane | x ∈ (Set.univ : Set Plane) ∧ ‖x‖ ^ 2 ≤ 1} =
      Metric.closedBall (0 : Plane) 1 := by
    simpa only [one_pow] using norm_square_sublevel 1 zero_le_one
  have H := ZLattice.covolume.tendsto_card_le_div' triangularModule
    (X := Set.univ) (F := fun x => ‖x‖ ^ 2)
    (fun _ _ _ _ => Set.mem_univ _)
    (by
      intro x r hr
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, mul_pow,
        finrank_euclideanSpace, Fintype.card_fin])
    (by rw [hunit]; exact Metric.isBounded_closedBall)
    (by rw [hunit]; exact Metric.isClosed_closedBall.measurableSet)
    (by
      rw [hunit, frontier_closedBall (0 : Plane) one_ne_zero]
      exact MeasureTheory.Measure.addHaar_sphere MeasureTheory.volume _ _)
  have hvol : MeasureTheory.volume.real (Metric.closedBall (0 : Plane) 1) = Real.pi := by
    rw [MeasureTheory.measureReal_def, EuclideanSpace.volume_closedBall_fin_two]
    simp [Real.pi_pos.le]
  rw [hunit, hvol, triangular_covolume, div_one] at H
  apply (H.comp (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  dsimp
  rw [norm_square_sublevel R hR, diskCount_eq_card _ triangular_locallyFinite,
    ← triangularModule_coe, Set.inter_comm]
  rfl

lemma triangular_densityOne : DensityOne triangularLattice := by
  have H := triangular_count_asymptotic.div_const Real.pi
  rw [div_self Real.pi_ne_zero] at H
  apply H.congr'
  exact Filter.Eventually.of_forall fun R => by dsimp; ring

lemma mem_diskPoints_iff (C : Set Plane) (hC : LocallyFinite C) (R : ℝ) (x : Plane) :
    x ∈ diskPoints C R ↔ x ∈ C ∧ ‖x‖ ≤ R := by
  simp [diskPoints, hC R, Metric.mem_closedBall, dist_zero_right]

lemma triangular_count_pos {R : ℝ} (hR : 0 ≤ R) : 0 < diskCount triangularLattice R := by
  apply Finset.card_pos.mpr
  refine ⟨0, (mem_diskPoints_iff _ triangular_locallyFinite _ _).mpr ?_⟩
  exact ⟨⟨(0, 0), triangularPoint_zero⟩, by simpa using hR⟩

lemma lattice_interior_count_ratio (M : ℝ) :
    Tendsto (fun R : ℝ => (diskCount triangularLattice (R - M) : ℝ) /
      (diskCount triangularLattice R : ℝ)) atTop (𝓝 1) := by
  have hshift : Tendsto (fun R : ℝ => R - M) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b + M)] with R hR
    linarith
  have hrat : Tendsto (fun R : ℝ => (R - M) / R) atTop (𝓝 1) := by
    have H := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub
      (tendsto_id.const_div_atTop M)
    simp only [sub_zero] at H
    apply H.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    dsimp only [id]
    field_simp [ne_of_gt hR]
  have H := ((triangular_count_asymptotic.comp hshift).mul (hrat.pow 2)).div
    triangular_count_asymptotic Real.pi_ne_zero
  simp only [one_pow, mul_one, div_self Real.pi_ne_zero] at H
  apply H.congr'
  filter_upwards [eventually_gt_atTop (|M| + 1)] with R hR
  have hR0 : 0 < R := by linarith [abs_nonneg M]
  have hRM : 0 < R - M := by linarith [le_abs_self M]
  have hc : (diskCount triangularLattice R : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (triangular_count_pos hR0.le)
  dsimp
  field_simp [ne_of_gt hR0, ne_of_gt hRM, hc]

lemma lattice_interior_count_ratio_ennreal (M : ℝ) :
    Tendsto (fun R : ℝ => (diskCount triangularLattice R : ℝ≥0∞)⁻¹ *
      (diskCount triangularLattice (R - M) : ℝ≥0∞)) atTop (𝓝 1) := by
  have H := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (lattice_interior_count_ratio M)
  rw [ENNReal.ofReal_one] at H
  apply H.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  have hc : 0 < (diskCount triangularLattice R : ℝ) := by
    exact_mod_cast triangular_count_pos hR
  dsimp only [Function.comp_apply]
  rw [ENNReal.ofReal_div_of_pos hc]
  simp only [ENNReal.ofReal_natCast, div_eq_mul_inv, mul_comm]

abbrev NonzeroSite := {x : Plane // x ∈ triangularLattice ∧ x ≠ 0}

lemma finite_lattice_row_ge (g : ℝ → ℝ) (F : Finset NonzeroSite) (M : ℝ)
    (hM : ∀ a ∈ F, ‖a.val‖ ≤ M) (R : ℝ) (x : Plane)
    (hx : x ∈ diskPoints triangularLattice (R - M)) :
    ∑ a ∈ F, ENNReal.ofReal (g (‖a.val‖ ^ 2)) ≤
      ∑ y ∈ (diskPoints triangularLattice R).erase x,
        ENNReal.ofReal (g (‖x - y‖ ^ 2)) := by
  have hx' := (mem_diskPoints_iff _ triangular_locallyFinite _ _).mp hx
  have hinj : Function.Injective (fun a : NonzeroSite => x - a.val) := by
    intro a b h
    exact Subtype.ext (sub_right_injective h)
  have hsub : F.image (fun a : NonzeroSite => x - a.val) ⊆
      (diskPoints triangularLattice R).erase x := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨a, ha, rfl⟩
    apply Finset.mem_erase.mpr
    constructor
    · intro he
      have : a.val = 0 := by exact sub_eq_self.mp he
      exact a.property.2 this
    · apply (mem_diskPoints_iff _ triangular_locallyFinite _ _).mpr
      refine ⟨triangularLattice_sub hx'.1 a.property.1, ?_⟩
      have := norm_sub_le x a.val
      linarith [hx'.2, hM a ha]
  calc
    _ = ∑ a ∈ F, ENNReal.ofReal (g (‖x - (x - a.val)‖ ^ 2)) := by simp
    _ = ∑ y ∈ F.image (fun a : NonzeroSite => x - a.val),
        ENNReal.ofReal (g (‖x - y‖ ^ 2)) := by
      rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
    _ ≤ _ := Finset.sum_le_sum_of_subset hsub

lemma finite_lattice_disk_energy_ge (g : ℝ → ℝ) (F : Finset NonzeroSite) (M : ℝ)
    (hM0 : 0 ≤ M) (hM : ∀ a ∈ F, ‖a.val‖ ≤ M) (R : ℝ) :
    ((diskCount triangularLattice R : ℝ≥0∞)⁻¹ *
      (diskCount triangularLattice (R - M) : ℝ≥0∞)) *
      (∑ a ∈ F, ENNReal.ofReal (g (‖a.val‖ ^ 2))) ≤
      diskEnergy g triangularLattice R := by
  have hsub : diskPoints triangularLattice (R - M) ⊆ diskPoints triangularLattice R := by
    intro x hx
    rw [mem_diskPoints_iff _ triangular_locallyFinite] at hx ⊢
    exact ⟨hx.1, by linarith [hx.2]⟩
  have H : (diskCount triangularLattice (R - M) : ℝ≥0∞) *
      (∑ a ∈ F, ENNReal.ofReal (g (‖a.val‖ ^ 2))) ≤
      ∑ x ∈ diskPoints triangularLattice R,
        ∑ y ∈ (diskPoints triangularLattice R).erase x,
          ENNReal.ofReal (g (‖x - y‖ ^ 2)) := by
    calc
      _ = ∑ x ∈ diskPoints triangularLattice (R - M),
          (∑ a ∈ F, ENNReal.ofReal (g (‖a.val‖ ^ 2))) := by simp [diskCount]
      _ ≤ ∑ x ∈ diskPoints triangularLattice (R - M),
          ∑ y ∈ (diskPoints triangularLattice R).erase x,
            ENNReal.ofReal (g (‖x - y‖ ^ 2)) :=
        Finset.sum_le_sum fun x hx => finite_lattice_row_ge g F M hM R x hx
      _ ≤ _ := Finset.sum_le_sum_of_subset hsub
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left H zero_le

lemma lattice_energy_lower (g : ℝ → ℝ) :
    latticeEnergy g ≤ energy g triangularLattice := by
  apply ENNReal.summable.tsum_le_of_sum_le
  intro F
  let M : ℝ := ∑ a ∈ F, ‖a.val‖
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hM : ∀ a ∈ F, ‖a.val‖ ≤ M := fun a ha =>
    Finset.single_le_sum (fun i _ => norm_nonneg i.val) ha
  have H := ENNReal.Tendsto.mul_const (lattice_interior_count_ratio_ennreal M)
    (b := ∑ a ∈ F, ENNReal.ofReal (g (‖a.val‖ ^ 2))) (Or.inl one_ne_zero)
  simp only [one_mul] at H
  rw [← H.liminf_eq]
  exact liminf_le_liminf (Filter.Eventually.of_forall
    (finite_lattice_disk_energy_ge g F M hM0 hM))

lemma lattice_energy_eq (g : ℝ → ℝ) :
    latticeEnergy g = energy g triangularLattice :=
  le_antisymm (lattice_energy_lower g) (lattice_energy_upper g)

end TriangularUniversal

open scoped BigOperators Topology NNReal ENNReal Polynomial
open Filter Finset MeasureTheory
noncomputable section
namespace TriangularUniversal.PositiveMixture

def difference (m : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, j => m j
  | r+1, j => difference m r j - difference m r (j+1)

def momentFunctional (m : ℕ → ℝ) : ℝ[X] →ₗ[ℝ] ℝ :=
  Polynomial.lsum fun j => LinearMap.mulRight ℝ (m j)

@[simp] lemma moment_monomial (m : ℕ → ℝ) (j : ℕ) (a : ℝ) :
    momentFunctional m (Polynomial.monomial j a) = a*m j := by
  simp [momentFunctional, Polynomial.lsum, Polynomial.sum_monomial_index]

@[simp] lemma moment_pow (m : ℕ → ℝ) (j : ℕ) :
    momentFunctional m (Polynomial.X^j) = m j := by
  rw [← Polynomial.monomial_one_right_eq_X_pow, moment_monomial, one_mul]

lemma moment_difference (m : ℕ → ℝ) (r j : ℕ) :
    momentFunctional m (Polynomial.X^j*(1-Polynomial.X)^r) = difference m r j := by
  induction r generalizing j with
  | zero => simp [difference]
  | succ r ih =>
    rw [show (Polynomial.X^j*(1-Polynomial.X)^(r+1) : ℝ[X]) =
      Polynomial.X^j*(1-Polynomial.X)^r-Polynomial.X^(j+1)*(1-Polynomial.X)^r by ring]
    rw [map_sub, ih, ih, difference]

@[simp] lemma moment_bernstein (m : ℕ → ℝ) (n p : ℕ) :
    momentFunctional m (bernsteinPolynomial ℝ n p) =
      (n.choose p : ℝ)*difference m (n-p) p := by
  rw [bernsteinPolynomial, mul_assoc]
  rw [show (n.choose p : ℝ[X]) = Polynomial.C (n.choose p : ℝ) by simp]
  rw [← Polynomial.smul_eq_C_mul, map_smul, moment_difference]
  rfl

def weight (m : ℕ → ℝ) (n p : ℕ) : ℝ :=
  (n.choose p : ℝ)*difference m (n-p) p

lemma weight_nonneg {m : ℕ → ℝ} (hm : ∀ r j, 0 ≤ difference m r j) (n p : ℕ) :
    0 ≤ weight m n p := mul_nonneg (Nat.cast_nonneg _) (hm _ _)

lemma weight_sum (m : ℕ → ℝ) (n : ℕ) :
    ∑ p ∈ range (n+1), weight m n p = m 0 := by
  simp_rw [weight, ← moment_bernstein]
  rw [← map_sum, bernsteinPolynomial.sum]
  simpa using moment_pow m 0

def bernsteinBasis (n d : ℕ) (x : ℝ) : ℝ :=
  (n.choose d : ℝ) * x^d * (1-x)^(n-d)

lemma bernsteinBasis_sum (n : ℕ) (x : ℝ) :
    ∑ d ∈ range (n+1), bernsteinBasis n d x = 1 := by
  calc
    _ = (x+(1-x))^n := by
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro d hd
      dsimp [bernsteinBasis]
      ring
    _ = 1 := by simp

lemma bernsteinBasis_nonneg (n d : ℕ) {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    0 ≤ bernsteinBasis n d x := by
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx.1 _))
    (pow_nonneg (by linarith [hx.2]) _)

lemma choose_ratio (n r d : ℕ) (hr : r ≤ n) (hd : r ≤ d) :
    (d.choose r : ℝ)/(n.choose r : ℝ)*(n.choose d : ℝ) =
      ((n-r).choose (d-r) : ℝ) := by
  have h : (n.choose d : ℝ)*(d.choose r : ℝ) =
      (n.choose r : ℝ)*((n-r).choose (d-r) : ℝ) := by
    exact_mod_cast Nat.choose_mul (n:=n) hd
  have hn : (n.choose r : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hr
  rw [div_mul_eq_mul_div]
  apply (div_eq_iff hn).mpr
  convert h using 1 <;> ring

lemma bernstein_monomial (n r : ℕ) (hr : r ≤ n) (x : ℝ) :
    ∑ d ∈ range (n+1), ((d.choose r : ℝ)/(n.choose r : ℝ))*bernsteinBasis n d x = x^r := by
  let f : ℕ → ℝ := fun d => ((d.choose r : ℝ)/(n.choose r : ℝ))*bernsteinBasis n d x
  have hlo : ∑ d ∈ range r, f d = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    simp [f, Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hd)]
  have heq : ∀ d, r ≤ d →
      f d = x^r * ((n-r).choose (d-r) : ℝ)*x^(d-r)*(1-x)^((n-r)-(d-r)) := by
    intro d hd
    dsimp [f,bernsteinBasis]
    rw [show n-d = (n-r)-(d-r) by omega]
    rw [show d = r+(d-r) by omega, pow_add]
    have hratio := choose_ratio n r d hr hd
    rw [show r+(d-r)=d by omega]
    calc
      _ = (((d.choose r : ℝ)/(n.choose r : ℝ))*(n.choose d : ℝ))*
        x^r*x^(d-r)*(1-x)^((n-r)-(d-r)) := by ring
      _ = _ := by rw [hratio]; ring
  change (∑ d ∈ range (n+1), f d) = _
  rw [← Finset.sum_range_add_sum_Ico f (show r ≤ n+1 by omega), hlo, zero_add]
  rw [Finset.sum_Ico_eq_sum_range]
  have he : n+1-r = n-r+1 := by omega
  rw [he]
  calc
    _ = x^r * ∑ j ∈ range (n-r+1), bernsteinBasis (n-r) j x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [heq _ (by omega)]
      simp only [Nat.add_sub_cancel_left, bernsteinBasis]
      ring
    _ = x^r := by rw [bernsteinBasis_sum, mul_one]

lemma weighted_binomial_moment (m : ℕ → ℝ) (n j : ℕ) (hjn : j ≤ n) :
    ∑ p ∈ range (n+1), ((p.choose j : ℝ)/(n.choose j : ℝ))*weight m n p = m j := by
  have hp : (∑ p ∈ range (n+1), ((p.choose j : ℝ)/(n.choose j : ℝ)) •
      bernsteinPolynomial ℝ n p) = Polynomial.X^j := by
    apply Polynomial.funext
    intro x
    simpa [Polynomial.eval_finsetSum, Polynomial.eval_smul, bernsteinPolynomial,
      bernsteinBasis] using bernstein_monomial n j hjn x
  apply_fun momentFunctional m at hp
  simpa [weight] using hp

abbrev I := Set.Icc (0 : ℝ) 1

def coordinate : C(I, ℝ) := ⟨Subtype.val, continuous_subtype_val⟩

def falling (n j : ℕ) : C(I, ℝ) :=
  ∏ r ∈ range j, ((1-(r : ℝ)/n)⁻¹) • (coordinate - ((r : ℝ)/n) • 1)

lemma falling_tendsto (j : ℕ) :
    Tendsto (fun n => falling n j) atTop (𝓝 (coordinate^j)) := by
  have hf (r : ℕ) : Tendsto (fun n : ℕ =>
      ((1-(r : ℝ)/n)⁻¹) • (coordinate - ((r : ℝ)/n) • (1 : C(I,ℝ)))) atTop
      (𝓝 coordinate) := by
    have h : Tendsto (fun n : ℕ => (r : ℝ)/n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have h₁ := (tendsto_const_nhds.sub h).inv₀ (by norm_num : (1 : ℝ)-0 ≠ 0)
    simpa using h₁.smul (tendsto_const_nhds.sub (h.smul_const (1 : C(I,ℝ))))
  simpa [falling] using tendsto_finsetProd (range j) (fun _ _ => hf _)

lemma falling_grid (n p j : ℕ) (hn : 0 < n) (hjn : j ≤ n) (hp : p ≤ n) :
    falling n j ⟨(p : ℝ)/n, div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
        (div_le_one (by positivity)).mpr (by exact_mod_cast hp)⟩ =
      (p.choose j : ℝ)/(n.choose j : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  simp only [falling, ContinuousMap.prod_apply, ContinuousMap.smul_apply,
    ContinuousMap.sub_apply, coordinate, ContinuousMap.coe_mk, ContinuousMap.one_apply,
    smul_eq_mul, mul_one]
  calc
    _ = ∏ r ∈ range j, ((p : ℝ)-r)/((n : ℝ)-r) := by
      apply Finset.prod_congr rfl
      intro r hr
      have hnr : (n : ℝ)-r ≠ 0 := by
        have : r < n := lt_of_lt_of_le (mem_range.mp hr) hjn
        exact sub_ne_zero.mpr (by exact_mod_cast this.ne')
      field_simp
    _ = (∏ r ∈ range j, ((p : ℝ)-r))/(∏ r ∈ range j, ((n : ℝ)-r)) := by
      rw [Finset.prod_div_distrib]
    _ = (p.descFactorial j : ℝ)/(n.descFactorial j : ℝ) := by
      rw [← descPochhammer_eval_eq_prod_range,
        ← descPochhammer_eval_eq_prod_range,
        descPochhammer_eval_eq_descFactorial,
        descPochhammer_eval_eq_descFactorial]
    _ = _ := by
      rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
      push_cast
      exact mul_div_mul_left _ _ (by positivity : (j.factorial : ℝ) ≠ 0)

def gridMeasure (m : ℕ → ℝ) (n : ℕ) : Measure I :=
  ∑ p : Fin (n+1), ENNReal.ofReal (weight m n p) • Measure.dirac (bernstein.z p)

instance gridMeasure_finite (m : ℕ → ℝ) (n : ℕ) : IsFiniteMeasure (gridMeasure m n) := by
  constructor
  simp only [gridMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  exact ENNReal.sum_lt_top.mpr (fun _ _ => ENNReal.ofReal_lt_top)

def gridFiniteMeasure (m : ℕ → ℝ) (n : ℕ) : FiniteMeasure I :=
  ⟨gridMeasure m n, inferInstance⟩

lemma gridMeasure_mass {m : ℕ → ℝ} (hm : ∀ r j, 0 ≤ difference m r j) (n : ℕ) :
    gridMeasure m n Set.univ = ENNReal.ofReal (m 0) := by
  simp only [gridMeasure, Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
    (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
    (f := fun p : Fin (n+1) => weight m n p) (fun p _ => weight_nonneg hm n p)]
  congr 1
  simpa [Finset.sum_range] using weight_sum m n

lemma gridFiniteMeasure_mass {m : ℕ → ℝ} (hm : ∀ r j, 0 ≤ difference m r j) (n : ℕ) :
    (gridFiniteMeasure m n).mass = (m 0).toNNReal := by
  apply ENNReal.coe_injective
  rw [FiniteMeasure.ennreal_mass]
  change gridMeasure m n _ = _
  rw [gridMeasure_mass hm]
  rfl

lemma integral_grid {m : ℕ → ℝ} (hm : ∀ r j, 0 ≤ difference m r j) (n : ℕ)
    (f : C(I,ℝ)) :
    ∫ x, f x ∂gridMeasure m n = ∑ p : Fin (n+1), weight m n p * f (bernstein.z p) := by
  rw [gridMeasure, integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro p hp
    simp [ENNReal.toReal_ofReal (weight_nonneg hm n p)]
  · intro p hp
    exact (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

lemma integral_falling {m : ℕ → ℝ} (hm : ∀ r j, 0 ≤ difference m r j)
    (n j : ℕ) (hn : 0 < n) (hjn : j ≤ n) :
    ∫ x, falling n j x ∂gridMeasure m n = m j := by
  rw [integral_grid hm]
  have he (p : Fin (n+1)) : falling n j (bernstein.z p) =
      (p.val.choose j : ℝ)/(n.choose j : ℝ) := falling_grid n p j hn hjn p.is_le
  simp_rw [he, mul_comm (weight m n _) ]
  simpa [Finset.sum_range] using weighted_binomial_moment m n j hjn

lemma grid_moments_tendsto {m : ℕ → ℝ} (hm : ∀ r j, 0 ≤ difference m r j) (j : ℕ) :
    Tendsto (fun n => ∫ x : I, (x : ℝ)^j ∂gridMeasure m n) atTop (𝓝 (m j)) := by
  have herr : Tendsto (fun n => ‖coordinate^j-falling n j‖*(m 0)) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := coordinate^j)).sub (falling_tendsto j)).norm.mul_const (m 0)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' _ _ herr
  · filter_upwards [] with n using norm_nonneg _
  · filter_upwards [eventually_gt_atTop 0, eventually_ge_atTop j] with n hn hjn
    rw [← integral_falling hm n j hn hjn]
    rw [← integral_sub (by exact (coordinate^j).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      ((falling n j).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    have h := norm_integral_le_of_norm_le_const (μ := gridMeasure m n)
      (C := ‖coordinate^j-falling n j‖)
      (Filter.Eventually.of_forall (fun x => (coordinate^j-falling n j).norm_coe_le_norm x))
    simpa [coordinate, Measure.real, gridMeasure_mass hm, ENNReal.toReal_ofReal (show 0 ≤ m 0 from hm 0 0)] using h

theorem hausdorff {m : ℕ → ℝ} (hm : ∀ r j, 0 ≤ difference m r j) :
    ∃ μ : FiniteMeasure I, (μ.mass : ℝ) = m 0 ∧
      ∀ j : ℕ, (∫ x : I, (x : ℝ)^j ∂(μ : Measure I)) = m j := by
  have h0 : 0 ≤ m 0 := hm 0 0
  obtain ⟨μ, hμ, hlim⟩ :=
    (isCompact_setOfPred_finiteMeasure_eq_of_compactSpace I (m 0).toNNReal).exists_mapClusterPt
      (Filter.le_principal_iff.mpr
        (show ∀ᶠ ν in Filter.map (gridFiniteMeasure m) atTop, ν.mass = (m 0).toNNReal from
          Filter.eventually_map.mpr (Filter.Eventually.of_forall (fun n => gridFiniteMeasure_mass hm n))))
  refine ⟨μ, by simpa [Real.toNNReal_of_nonneg h0] using congrArg NNReal.toReal hμ, fun j => ?_⟩
  have hw := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp
    (show Tendsto (id : FiniteMeasure I → FiniteMeasure I) (𝓝 μ) (𝓝 μ) from tendsto_id) (ContinuousMap.equivBoundedOfCompact I ℝ (coordinate^j))
  have hc := hlim.tendsto_comp hw
  have hd := grid_moments_tendsto hm j
  apply eq_of_nhds_neBot
  exact (show NeBot (𝓝 (∫ x : I, (x : ℝ)^j ∂(μ : Measure I)) ⊓ Filter.map (fun n => ∫ x : I, (x : ℝ)^j ∂gridMeasure m n) atTop) from hc).mono (inf_le_inf_left _ hd)

def CM (g : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) g (Set.Ioi 0) ∧
  ∀ r : ℕ, ∀ t : ℝ, 0 < t → 0 ≤ (-1 : ℝ)^r * iteratedDeriv r g t

lemma CM.deriv_differentiableOn {g : ℝ → ℝ} (hg : CM g) (r : ℕ) :
    DifferentiableOn ℝ (iteratedDeriv r g) (Set.Ioi 0) := by
  have hd := hg.1.differentiableOn_iteratedDerivWithin (m := r)
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl r) isOpen_Ioi.uniqueDiffOn
  exact hd.congr (fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioi hx).symm)

lemma CM.signed_antitone {g : ℝ → ℝ} (hg : CM g) (r : ℕ) :
    AntitoneOn (fun x => (-1 : ℝ)^r * iteratedDeriv r g x) (Set.Ioi 0) := by
  have hd := (hg.deriv_differentiableOn r).const_mul ((-1 : ℝ)^r)
  apply antitoneOn_of_deriv_nonpos (convex_Ioi _) hd.continuousOn
  · simpa only [interior_Ioi] using hd
  · intro x hx
    have hx' : 0 < x := by simpa only [interior_Ioi, Set.mem_Ioi] using hx
    have hdx := (hg.deriv_differentiableOn r x hx').differentiableAt (Ioi_mem_nhds hx')
    rw [deriv_const_mul_field, ← iteratedDeriv_succ]
    have hs := hg.2 (r+1) x hx'
    simp only [pow_succ, mul_neg_one] at hs
    linarith

lemma CM.shift {g : ℝ → ℝ} (hg : CM g) {d : ℝ} (hd : 0 ≤ d) :
    CM (fun x => g (x+d)) := by
  constructor
  · exact hg.1.comp ((contDiff_id.add contDiff_const).contDiffOn) (fun x hx => add_pos_of_pos_of_nonneg hx hd)
  · intro r x hx
    rw [iteratedDeriv_comp_add_const]
    exact hg.2 r _ (by linarith)

lemma CM.sub_shift {g : ℝ → ℝ} (hg : CM g) {d : ℝ} (hd : 0 ≤ d) :
    CM (fun x => g x-g (x+d)) := by
  refine ⟨hg.1.sub (hg.shift hd).1, ?_⟩
  intro r x hx
  have hgx : ContDiffAt ℝ r g x := (hg.1.contDiffAt (Ioi_mem_nhds hx)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl r)
  have hgdx : ContDiffAt ℝ r (fun x => g (x+d)) x :=
    ((hg.shift hd).1.contDiffAt (Ioi_mem_nhds hx)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl r)
  rw [iteratedDeriv_fun_sub hgx hgdx, iteratedDeriv_comp_add_const, mul_sub]
  exact sub_nonneg.mpr (hg.signed_antitone r hx (add_pos_of_pos_of_nonneg hx hd) (le_add_of_nonneg_right hd))

lemma difference_shift (m : ℕ → ℝ) (r j : ℕ) :
    difference (fun k => m k-m (k+1)) r j = difference m (r+1) j := by
  induction r generalizing j with
  | zero => rfl
  | succ r ih => simp only [difference, ih]

lemma CM.sample_difference {g : ℝ → ℝ} (hg : CM g) {ε d : ℝ}
    (hε : 0 < ε) (hd : 0 ≤ d) (r j : ℕ) :
    0 ≤ difference (fun j : ℕ => g (ε+j*d)) r j := by
  induction r generalizing g j with
  | zero => simpa [difference] using hg.2 0 (ε+j*d) (by positivity)
  | succ r ih =>
    have h := ih (hg.sub_shift hd) j
    have he : (fun j : ℕ => g (ε+j*d)-g (ε+j*d+d)) =
        (fun j : ℕ => g (ε+j*d)-g (ε+((j+1 : ℕ) : ℝ)*d)) := by
      funext j
      congr 2; push_cast; ring
    rw [he, difference_shift] at h
    exact h

abbrev Positive := {t : ℝ // 0 < t}

def powerTest (t : Positive) : C(I, ℝ) :=
  ⟨fun v => (v : ℝ) ^ (t : ℝ), (Real.continuous_rpow_const t.property.le).comp continuous_subtype_val⟩

lemma continuous_powerTest : Continuous powerTest := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_subtype_val.comp continuous_snd).rpow
    (continuous_subtype_val.comp continuous_fst) (fun p => Or.inr p.1.property)

def unitPower (n : ℕ) : C(I, I) :=
  ⟨fun v => ⟨(v : ℝ)^n, ⟨pow_nonneg v.property.1 _, pow_le_one₀ v.property.1 v.property.2⟩⟩,
    (continuous_subtype_val.pow n).subtype_mk _⟩

lemma mass_map_unitPower (μ : FiniteMeasure I) (n : ℕ) :
    (μ.map (unitPower n)).mass = μ.mass := by
  exact μ.map_apply (unitPower n).continuous.measurable MeasurableSet.univ

lemma integral_power_map (μ : FiniteMeasure I) {n : ℕ} (hn : 0 < n) (j : ℕ) :
    ∫ v : I, (v : ℝ) ^ ((j : ℝ)/n) ∂(μ.map (unitPower n) : Measure I) =
      ∫ v : I, (v : ℝ)^j ∂(μ : Measure I) := by
  rw [FiniteMeasure.toMeasure_map]
  have hmap := integral_map (μ := (μ : Measure I)) (f := fun v : I => (v : ℝ)^((j : ℝ)/n))
    (unitPower n).continuous.measurable.aemeasurable
    (((Real.continuous_rpow_const (by positivity : 0 ≤ (j : ℝ)/n)).comp continuous_subtype_val).aestronglyMeasurable)
  rw [hmap]
  congr 1
  funext v
  change ((v : ℝ)^n) ^ ((j : ℝ)/n) = (v : ℝ)^j
  rw [← Real.rpow_natCast, ← Real.rpow_mul v.property.1]
  rw [mul_div_cancel₀ _ (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0), Real.rpow_natCast]

def gridTime (t : ℝ) (n : ℕ) : ℝ := (⌊t*((n : ℝ)+1)⌋₊ + 1 : ℕ) / ((n : ℝ)+1)

lemma gridTime_pos (t : ℝ) (n : ℕ) : 0 < gridTime t n := by
  unfold gridTime
  positivity

lemma gridTime_tendsto {t : ℝ} (ht : 0 ≤ t) : Tendsto (gridTime t) atTop (𝓝 t) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hf := (tendsto_nat_floor_mul_div_atTop ht).comp hn
  have hi := tendsto_inv_atTop_zero.comp hn
  convert hf.add hi using 1
  · funext n
    simp [gridTime, add_div, one_div]
  · simp

theorem mixture_of_differences {F : ℝ → ℝ}
    (hF : ContinuousOn F (Set.Ici 0))
    (hD : ∀ d : ℝ, 0 < d → ∀ r j : ℕ,
      0 ≤ difference (fun j : ℕ => F (j*d)) r j) :
    ∃ ρ : FiniteMeasure I, (ρ.mass : ℝ) = F 0 ∧
      ∀ t : ℝ, 0 < t → ∫ v : I, (v : ℝ)^t ∂(ρ : Measure I) = F t := by
  have h0 : 0 ≤ F 0 := by simpa [difference] using hD 1 zero_lt_one 0 0
  have hex (n : ℕ) := hausdorff (hD (1/((n : ℝ)+1)) (by positivity))
  choose η hηmass hηmoment using hex
  let ρseq (n : ℕ) : FiniteMeasure I := (η n).map (unitPower (n+1))
  have hm (n : ℕ) : ((ρseq n).mass : ℝ) = F 0 := by
    simpa [ρseq, mass_map_unitPower] using hηmass n
  obtain ⟨ρ, hρ, hlim⟩ :=
    (isCompact_setOfPred_finiteMeasure_eq_of_compactSpace I (F 0).toNNReal).exists_mapClusterPt
      (Filter.le_principal_iff.mpr
        (show ∀ᶠ ν in Filter.map ρseq atTop, ν.mass = (F 0).toNNReal from
          Filter.eventually_map.mpr (Filter.Eventually.of_forall (fun n => by
            apply NNReal.eq
            simpa [Real.toNNReal_of_nonneg h0] using hm n))))
  refine ⟨ρ, by simpa [Real.toNNReal_of_nonneg h0] using congrArg NNReal.toReal hρ, ?_⟩
  intro t ht
  let tj (n : ℕ) : ℕ := ⌊t*((n : ℝ)+1)⌋₊+1
  let tn (n : ℕ) : Positive := ⟨gridTime t n, gridTime_pos t n⟩
  have he (n : ℕ) : ∫ v : I, (v : ℝ)^(gridTime t n) ∂(ρseq n : Measure I) = F (gridTime t n) := by
    have h := integral_power_map (η n) (Nat.succ_pos n) (tj n)
    have hh := hηmoment n (tj n)
    simp only [div_eq_mul_inv] at h hh
    simpa [ρseq, gridTime, tj, Nat.cast_add, Nat.cast_one, div_eq_mul_inv] using h.trans hh
  have htest : Tendsto (fun n => powerTest (tn n)) atTop (𝓝 (powerTest ⟨t, ht⟩)) :=
    continuous_powerTest.tendsto _ |>.comp (tendsto_subtype_rng.mpr (gridTime_tendsto ht.le))
  have herr : Tendsto (fun n => ‖powerTest ⟨t, ht⟩ - powerTest (tn n)‖ * F 0) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := powerTest ⟨t, ht⟩)).sub htest).norm.mul_const (F 0)
  have hdiff : Tendsto (fun n =>
      (∫ v : I, (v : ℝ)^t ∂(ρseq n : Measure I)) - F (gridTime t n)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) _ herr
    intro n
    rw [← he n]
    change ‖(∫ v, powerTest ⟨t, ht⟩ v ∂(ρseq n : Measure I)) -
      (∫ v, powerTest (tn n) v ∂(ρseq n : Measure I))‖ ≤ _
    rw [← integral_sub
      ((powerTest ⟨t, ht⟩).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      ((powerTest (tn n)).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    have hb := norm_integral_le_of_norm_le_const (μ := (ρseq n : Measure I))
      (C := ‖powerTest ⟨t, ht⟩ - powerTest (tn n)‖)
      (Filter.Eventually.of_forall (fun v => (powerTest ⟨t, ht⟩ - powerTest (tn n)).norm_coe_le_norm v))
    simpa only [Measure.real, ← FiniteMeasure.ennreal_mass, ENNReal.coe_toReal, hm, ContinuousMap.sub_apply] using hb
  have hFt : Tendsto (fun n => F (gridTime t n)) atTop (𝓝 (F t)) :=
    (hF.continuousAt (Ici_mem_nhds ht)).tendsto.comp (gridTime_tendsto ht.le)
  have hd : Tendsto (fun n => ∫ v : I, (v : ℝ)^t ∂(ρseq n : Measure I)) atTop (𝓝 (F t)) := by
    convert hdiff.add hFt using 1 <;> simp
  have hw := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp
    (show Tendsto (id : FiniteMeasure I → FiniteMeasure I) (𝓝 ρ) (𝓝 ρ) from tendsto_id)
    (ContinuousMap.equivBoundedOfCompact I ℝ (powerTest ⟨t, ht⟩))
  have hc := hlim.tendsto_comp hw
  apply eq_of_nhds_neBot
  exact (show NeBot (𝓝 (∫ v : I, (v : ℝ)^t ∂(ρ : Measure I)) ⊓
    Filter.map (fun n => ∫ v : I, (v : ℝ)^t ∂(ρseq n : Measure I)) atTop) from hc).mono
      (inf_le_inf_left _ hd)

theorem CM.shifted_mixture {g : ℝ → ℝ} (hg : CM g) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : FiniteMeasure I, (ρ.mass : ℝ) = g ε ∧
      ∀ t : ℝ, 0 < t → ∫ v : I, (v : ℝ)^t ∂(ρ : Measure I) = g (ε+t) := by
  have hc : ContinuousOn (fun t => g (ε+t)) (Set.Ici 0) :=
    hg.1.continuousOn.comp (continuous_const.add continuous_id).continuousOn
      (fun t ht => add_pos_of_pos_of_nonneg hε ht)
  have hd (d : ℝ) (hd : 0 < d) (r j : ℕ) :
      0 ≤ difference (fun j : ℕ => g (ε+j*d)) r j :=
    hg.sample_difference hε hd.le r j
  simpa using mixture_of_differences hc hd

end TriangularUniversal.PositiveMixture

open MeasureTheory
namespace TriangularUniversal
open PositiveMixture

def powerPotential (v : I) (t : ℝ) : ℝ := (v : ℝ)^t

lemma powerPotential_continuous {t : ℝ} (ht : 0 ≤ t) :
    Continuous (fun v : I => powerPotential v t) :=
  (Real.continuous_rpow_const ht).comp continuous_subtype_val

lemma measurable_diskEnergy_power (C : Set Plane) (R : ℝ) :
    Measurable (fun v : I => diskEnergy (powerPotential v) C R) := by
  unfold diskEnergy
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro x hx
  apply Finset.measurable_sum
  intro y hy
  exact ENNReal.continuous_ofReal.measurable.comp (powerPotential_continuous (sq_nonneg _)).measurable

lemma lintegral_power_eq (ρ : FiniteMeasure I) (F : ℝ → ℝ)
    (hF : ∀ t : ℝ, 0 < t → ∫ v : I, (v : ℝ)^t ∂(ρ : Measure I) = F t)
    {t : ℝ} (ht : 0 < t) :
    ∫⁻ v : I, ENNReal.ofReal (powerPotential v t) ∂(ρ : Measure I) = ENNReal.ofReal (F t) := by
  rw [← hF t ht]
  exact (ofReal_integral_eq_lintegral_ofReal
    ((powerTest ⟨t, ht⟩).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (Filter.Eventually.of_forall (fun v => Real.rpow_nonneg v.property.1 _))).symm

lemma lintegral_diskEnergy_power (ρ : FiniteMeasure I) (F : ℝ → ℝ)
    (hF : ∀ t : ℝ, 0 < t → ∫ v : I, (v : ℝ)^t ∂(ρ : Measure I) = F t)
    (C : Set Plane) (R : ℝ) :
    ∫⁻ v : I, diskEnergy (powerPotential v) C R ∂(ρ : Measure I) = diskEnergy F C R := by
  unfold diskEnergy
  rw [lintegral_const_mul]
  · congr 1
    rw [lintegral_finsetSum]
    · apply Finset.sum_congr rfl
      intro x hx
      rw [lintegral_finsetSum]
      · apply Finset.sum_congr rfl
        intro y hy
        exact lintegral_power_eq ρ F hF (sq_pos_of_pos (norm_pos_iff.mpr
          (sub_ne_zero.mpr (Finset.ne_of_mem_erase hy).symm)))
      · intro y hy
        exact (ENNReal.continuous_ofReal.measurable.comp
          (powerPotential_continuous (sq_nonneg _)).measurable)
    · intro x hx
      apply Finset.measurable_sum
      intro y hy
      exact ENNReal.continuous_ofReal.measurable.comp
        (powerPotential_continuous (sq_nonneg _)).measurable
  · apply Finset.measurable_sum
    intro x hx
    apply Finset.measurable_sum
    intro y hy
    exact ENNReal.continuous_ofReal.measurable.comp
      (powerPotential_continuous (sq_nonneg _)).measurable

lemma mixture_energy_lower (ρ : FiniteMeasure I) (F : ℝ → ℝ)
    (hF : ∀ t : ℝ, 0 < t → ∫ v : I, (v : ℝ)^t ∂(ρ : Measure I) = F t)
    (C : Set Plane) :
    ∫⁻ v : I, energy (powerPotential v) C ∂(ρ : Measure I) ≤ energy F C := by
  have h := lintegral_liminf_le (μ := (ρ : Measure I)) (u := (atTop : Filter ℝ))
    (fun R : ℝ => measurable_diskEnergy_power C R)
  simpa only [energy, lintegral_diskEnergy_power ρ F hF C] using h

instance nonzeroSite_countable : Countable NonzeroSite :=
  ((Set.countable_range triangularPoint).mono (fun _ h => h.1)).to_subtype

lemma lintegral_latticeEnergy_power (ρ : FiniteMeasure I) (F : ℝ → ℝ)
    (hF : ∀ t : ℝ, 0 < t → ∫ v : I, (v : ℝ)^t ∂(ρ : Measure I) = F t) :
    ∫⁻ v : I, latticeEnergy (powerPotential v) ∂(ρ : Measure I) = latticeEnergy F := by
  unfold latticeEnergy
  rw [lintegral_tsum]
  · apply tsum_congr
    intro a
    exact lintegral_power_eq ρ F hF (sq_pos_of_pos (norm_pos_iff.mpr a.property.2))
  · intro a
    exact (ENNReal.continuous_ofReal.measurable.comp
      (powerPotential_continuous (sq_nonneg _)).measurable).aemeasurable

theorem shifted_mixture_energy (g : ℝ → ℝ) (hg : AdmissiblePotential g)
    {ε : ℝ} (hε : 0 < ε) (C : Set Plane) :
    ∃ ρ : FiniteMeasure I, (ρ.mass : ℝ) = g ε ∧
      (∫⁻ v : I, latticeEnergy (powerPotential v) ∂(ρ : Measure I)) =
        latticeEnergy (fun t => g (ε+t)) ∧
      (∫⁻ v : I, energy (powerPotential v) C ∂(ρ : Measure I)) ≤
        energy (fun t => g (ε+t)) C := by
  obtain ⟨ρ, hm, hρ⟩ := CM.shifted_mixture ⟨hg.1, hg.2.2⟩ hε
  exact ⟨ρ, hm, lintegral_latticeEnergy_power ρ _ hρ, mixture_energy_lower ρ _ hρ C⟩
end TriangularUniversal

namespace TriangularUniversal
open PositiveMixture

lemma potential_antitone {g : ℝ → ℝ} (hg : AdmissiblePotential g) :
    AntitoneOn g (Set.Ioi 0) := by
  simpa using (CM.signed_antitone ⟨hg.1, hg.2.2⟩ 0)

lemma diskEnergy_mono {f g : ℝ → ℝ} (hfg : ∀ t, 0 < t → f t ≤ g t)
    (C : Set Plane) (R : ℝ) : diskEnergy f C R ≤ diskEnergy g C R := by
  unfold diskEnergy
  gcongr with x hx y hy
  exact hfg _ (sq_pos_of_pos (norm_pos_iff.mpr
    (sub_ne_zero.mpr (Finset.ne_of_mem_erase hy).symm)))

lemma energy_mono {f g : ℝ → ℝ} (hfg : ∀ t, 0 < t → f t ≤ g t) (C : Set Plane) :
    energy f C ≤ energy g C :=
  liminf_le_liminf (Filter.Eventually.of_forall (diskEnergy_mono hfg C))

lemma latticeEnergy_mono {f g : ℝ → ℝ} (hfg : ∀ t, 0 < t → f t ≤ g t) :
    latticeEnergy f ≤ latticeEnergy g := by
  apply ENNReal.tsum_le_tsum
  intro a
  exact ENNReal.ofReal_le_ofReal (hfg _ (sq_pos_of_pos (norm_pos_iff.mpr a.property.2)))

lemma shifted_energy_le {g : ℝ → ℝ} (hg : AdmissiblePotential g)
    {ε : ℝ} (hε : 0 ≤ ε) (C : Set Plane) :
    energy (fun t => g (ε+t)) C ≤ energy g C := by
  apply energy_mono
  intro t ht
  exact potential_antitone hg ht (add_pos_of_nonneg_of_pos hε ht) (le_add_of_nonneg_left hε)

lemma latticeEnergy_shift_iSup {g : ℝ → ℝ} (hg : AdmissiblePotential g) :
    latticeEnergy g = ⨆ n : ℕ, latticeEnergy (fun t => g (1/((n:ℝ)+1)+t)) := by
  apply le_antisymm
  · apply ENNReal.summable.tsum_le_of_sum_le
    intro F
    have hc (a : NonzeroSite) :
        Tendsto (fun n : ℕ => ENNReal.ofReal (g (1/((n:ℝ)+1)+‖a.val‖^2))) atTop
          (𝓝 (ENNReal.ofReal (g (‖a.val‖^2)))) := by
      have ht : 0 < ‖a.val‖^2 := sq_pos_of_pos (norm_pos_iff.mpr a.property.2)
      have hg' := hg.1.continuousOn.continuousAt (IsOpen.mem_nhds isOpen_Ioi ht)
      apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      apply hg'.tendsto.comp
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).add_const (‖a.val‖^2)
    have hf := tendsto_finsetSum F (fun a _ => hc a)
    apply le_of_tendsto hf
    apply Filter.Eventually.of_forall
    intro n
    exact (ENNReal.sum_le_tsum F).trans (le_iSup (fun n : ℕ =>
      latticeEnergy (fun t => g (1/((n:ℝ)+1)+t))) n)
  · apply iSup_le
    intro n
    apply latticeEnergy_mono
    intro t ht
    have hε : 0 < 1/((n:ℝ)+1) := by positivity
    exact potential_antitone hg ht (add_pos hε ht) (le_add_of_nonneg_left hε.le)

end TriangularUniversal
end
end

end OAI
