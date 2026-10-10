import OAI.Combinatorics.PolynomialVacuum.Bridge.BridgeRenewalFactorization

namespace OAI

namespace PolynomialVacuumBridge.Corridor.BridgeWord

noncomputable def mass (A : BridgeWord) : ℝ := criticalActivity^A.word.length
@[simp] theorem mass_one : mass 1=1 := by simp [mass]
@[simp] theorem mass_mul (A B : BridgeWord) : mass (A*B)=mass A*mass B := by simp [mass,pow_add]
theorem mass_pos (A : BridgeWord) : 0 < mass A := pow_pos criticalActivity_pos _
@[simp] theorem mass_prod (L : List BridgeWord) : mass L.prod=(L.map mass).prod := by
  induction L with | nil => simp | cons A L ih => simp [ih]

noncomputable def massConstant : ℝ := (Real.cos (3*Real.pi/8))⁻¹+1

theorem cos_sigma_pos : 0<Real.cos (3*Real.pi/8) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> nlinarith [Real.pi_pos]
theorem massConstant_pos : 0 < massConstant := add_pos (inv_pos.mpr cos_sigma_pos) zero_lt_one

theorem fixed_height_mass_bound (h : ℕ) (S : Finset BridgeWord)
    (hh : ∀ A∈S, A.height=h) : (∑ A∈S, mass A)≤ massConstant := by
  classical
  by_cases hp : h=0
  · have hS : S⊆{1} := by
      intro A hA
      simp only [Finset.mem_singleton]
      by_contra hn
      have := positive_of_nonempty hn
      rw [hh A hA,hp] at this
      omega
    calc
      (∑ A∈S, mass A)≤∑ A∈({1} : Finset BridgeWord), mass A :=
        Finset.sum_le_sum_of_subset_of_nonneg hS (fun A _ _ => (mass_pos A).le)
      _≤ massConstant := by simp only [Finset.sum_singleton,mass_one]; unfold massConstant; linarith [inv_pos.mpr cos_sigma_pos]
  have hpos : 1≤h := Nat.one_le_iff_ne_zero.mpr hp
  let V := S.biUnion (fun A => (traced bottomSource A.word).toFinset)
  have hV : ∀ v∈V, InStrip h v := by
    intro v hv
    obtain ⟨A,hA,hv⟩ := Finset.mem_biUnion.mp hv
    have hi := A.inStrip v (List.mem_toFinset.mp hv)
    rw [hh A hA] at hi
    simpa only [InStrip,layer_boxIndex] using hi
  obtain ⟨M,hM⟩ := finite_vertices_in_window h V hV
  have hmem : ∀ A∈S, A.word∈sourceExits (vertexWindow h M) bottomSource := by
    intro A hA
    have ht : (terminalGerm bottomSource A.word).1∉vertexWindow h M := by
      intro ht
      have hi := (vertexWindow_strip h M _ ht).2
      rw [A.terminal] at hi
      norm_num [boxIndex] at hi
      rw [hh A hA] at hi
      omega
    apply (mem_sourceExits _ _ _).mpr
    refine ⟨stopped_of_trace _ _ _ A.distinct ?_ ht,ht⟩
    intro v hv
    exact hM (Finset.mem_biUnion.mpr ⟨A,hA,List.mem_toFinset.mpr hv⟩)
  have hi : Set.InjOn BridgeWord.word S := fun _ _ _ _ he => ext he
  have he : (∑ A∈S,mass A)=∑ w∈S.image BridgeWord.word,criticalActivity^w.length :=
    by simpa only [mass] using (Finset.sum_image (f := fun w : List Bool => criticalActivity^w.length) hi).symm
  rw [he]
  calc
    (∑ w∈S.image BridgeWord.word,criticalActivity^w.length)≤
        ∑ w∈sourceExits (vertexWindow h M) bottomSource,criticalActivity^w.length := by
      apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun w _ _ => (pow_pos criticalActivity_pos _).le)
      intro w hw
      obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hw
      exact hmem A hA
    _≤ (Real.cos (3*Real.pi/8))⁻¹ := boundary_source_weight_bound _ bottomSource
      (vertexWindow_convex h M) (bottomSource_mem_window h M hpos)
      (bottomSource_outside_of_strip h _ (vertexWindow_strip h M))
    _≤ massConstant := by unfold massConstant; linarith

theorem bounded_height_mass_bound (H : ℕ) (S : Finset BridgeWord)
    (hH : ∀ A∈S, A.height≤H) : (∑ A∈S,mass A)≤ massConstant*(H+1) := by
  classical
  calc
    (∑ A∈S,mass A) = ∑ h∈Finset.range (H+1), ∑ A∈S.filter (fun A => A.height=h),mass A := by
      symm
      apply Finset.sum_fiberwise_of_maps_to
      intro A hA
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hH A hA))
    _≤∑ h∈Finset.range (H+1),massConstant := by
      apply Finset.sum_le_sum
      intro h hh
      exact fixed_height_mass_bound h _ (fun A hA => (Finset.mem_filter.mp hA).2)
    _=massConstant*(H+1) := by simp; ring

end PolynomialVacuumBridge.Corridor.BridgeWord

end OAI
