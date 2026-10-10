import Mathlib

namespace OAI

open Set Filter MeasureTheory

namespace Invariant233.MultiplicationPurePoint

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem topologicalClosure_iSup_eigenspace_eq_top
    (f : X → ℂ) (hf : Measurable f) {C : Set ℂ} (hC : C.Countable)
    (hmem : ∀ᵐ x ∂μ, f x ∈ C)
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (hT : ∀ v : Lp E 2 μ, (T v : X → E) =ᵐ[μ] fun x => f x • v x) :
    (⨆ y : C, Module.End.eigenspace T.toLinearMap y.val).topologicalClosure = ⊤ := by
  let : Countable C := hC.to_subtype
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro v hv
  have hfiber (y : C) : ∀ᵐ x ∂μ, f x = y.val → v x = 0 := by
    let s : Set X := f ⁻¹' {y.val}
    have hs : MeasurableSet s := hf (measurableSet_singleton _)
    have hvi : MemLp (s.indicator (fun x => v x)) 2 μ := (Lp.memLp v).indicator hs
    let w : Lp E 2 μ := MemLp.toLp (s.indicator (fun x => v x)) hvi
    have hw : (w : X → E) =ᵐ[μ] s.indicator (fun x => v x) := hvi.coeFn_toLp
    have heigen : w ∈ Module.End.eigenspace T.toLinearMap y.val := by
      rw [Module.End.mem_eigenspace_iff]
      apply Lp.ext
      filter_upwards [hT w, Lp.coeFn_smul y.val w, hw] with x hTx hsx hwx
      change (T w : X → E) x = (y.val • w : Lp E 2 μ) x
      rw [hTx, hsx]
      change f x • w x = y.val • w x
      by_cases hx : x ∈ s
      · have hxy : f x = y.val := hx
        rw [hxy]
      · have hw0 : w x = 0 := hwx.trans (Set.indicator_of_notMem hx _)
        simp only [hw0, smul_zero]
    have hinner : inner ℂ w v = 0 :=
      (Submodule.mem_orthogonal _ _).1 hv w (Submodule.mem_iSup_of_mem y heigen)
    have hself : inner ℂ w w = inner ℂ w v := by
      rw [L2.inner_def, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hw] with x hwx
      by_cases hx : x ∈ s
      · have hwv : w x = v x := hwx.trans (Set.indicator_of_mem hx _)
        rw [hwv]
      · have hw0 : w x = 0 := hwx.trans (Set.indicator_of_notMem hx _)
        simp only [hw0, inner_zero_left]
    have hw_eq_zero : w = 0 := inner_self_eq_zero.1 (hself.trans hinner)
    have hwzero : (w : X → E) =ᵐ[μ] 0 := by
      rw [hw_eq_zero]
      exact Lp.coeFn_zero E 2 μ
    filter_upwards [hw, hwzero] with x hwx hz hx
    have hxs : x ∈ s := hx
    exact (hwx.trans (Set.indicator_of_mem hxs _)).symm.trans hz
  have hall : ∀ᵐ x ∂μ, ∀ y : C, f x = y.val → v x = 0 := ae_all_iff.2 hfiber
  apply Lp.ext
  filter_upwards [hmem, hall, Lp.coeFn_zero E 2 μ] with x hx hall hz
  exact (hall ⟨f x, hx⟩ rfl).trans hz.symm

theorem topologicalClosure_iSup_eigenspace_eq_top_of_basis
    {ι : Type*} [Countable ι] (b : HilbertBasis ι ℂ E)
    (f : ι → X → ℂ) (hf : ∀ i, Measurable (f i))
    {C : Set ℂ} (hC : C.Countable)
    (hmem : ∀ i, ∀ᵐ x ∂μ, f i x ∈ C)
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (hT : ∀ (v : Lp E 2 μ) i, ∀ᵐ x ∂μ,
      inner ℂ (b i) (T v x) = f i x * inner ℂ (b i) (v x)) :
    (⨆ y : C, Module.End.eigenspace T.toLinearMap y.val).topologicalClosure = ⊤ := by
  let : Countable C := hC.to_subtype
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro v hv
  have hfiber (i : ι) (y : C) :
      ∀ᵐ x ∂μ, f i x = y.val → inner ℂ (b i) (v x) = 0 := by
    let s : Set X := f i ⁻¹' {y.val}
    have hs : MeasurableSet s := hf i (measurableSet_singleton _)
    let P : E →L[ℂ] E := InnerProductSpace.rankOne ℂ (b i) (b i)
    have hvp : MemLp (fun x => inner ℂ (b i) (v x) • b i) 2 μ := P.comp_memLp v
    have hvi : MemLp (s.indicator (fun x => inner ℂ (b i) (v x) • b i)) 2 μ :=
      hvp.indicator hs
    let w : Lp E 2 μ :=
      MemLp.toLp (s.indicator (fun x => inner ℂ (b i) (v x) • b i)) hvi
    have hw : (w : X → E) =ᵐ[μ] s.indicator (fun x => inner ℂ (b i) (v x) • b i) :=
      hvi.coeFn_toLp
    have heigen : w ∈ Module.End.eigenspace T.toLinearMap y.val := by
      rw [Module.End.mem_eigenspace_iff]
      apply Lp.ext
      have hTall : ∀ᵐ x ∂μ, ∀ j, inner ℂ (b j) (T w x) =
          f j x * inner ℂ (b j) (w x) := ae_all_iff.2 (hT w)
      filter_upwards [hTall, Lp.coeFn_smul y.val w, hw] with x hTx hsx hwx
      change (T w : X → E) x = (y.val • w : Lp E 2 μ) x
      rw [hsx]
      apply b.repr.injective
      ext j
      rw [b.repr_apply_apply, b.repr_apply_apply, hTx j]
      change f j x * inner ℂ (b j) (w x) = inner ℂ (b j) (y.val • w x)
      rw [inner_smul_right]
      by_cases hx : x ∈ s
      · have hwv : w x = inner ℂ (b i) (v x) • b i :=
          hwx.trans (Set.indicator_of_mem hx _)
        by_cases hji : j = i
        · subst j
          have hxy : f i x = y.val := hx
          rw [hxy]
        · rw [hwv, inner_smul_right, b.orthonormal.inner_eq_zero hji]
          simp only [mul_zero]
      · have hw0 : w x = 0 := hwx.trans (Set.indicator_of_notMem hx _)
        simp only [hw0, inner_zero_right, mul_zero]
    have hinner : inner ℂ w v = 0 :=
      (Submodule.mem_orthogonal _ _).1 hv w (Submodule.mem_iSup_of_mem y heigen)
    have hself : inner ℂ w w = inner ℂ w v := by
      rw [L2.inner_def, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hw] with x hwx
      by_cases hx : x ∈ s
      · have hwv : w x = inner ℂ (b i) (v x) • b i :=
          hwx.trans (Set.indicator_of_mem hx _)
        rw [hwv, inner_smul_left, inner_smul_right, inner_smul_left]
        rw [inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
        norm_num
      · have hw0 : w x = 0 := hwx.trans (Set.indicator_of_notMem hx _)
        simp only [hw0, inner_zero_left]
    have hw_eq_zero : w = 0 := inner_self_eq_zero.1 (hself.trans hinner)
    have hwzero : (w : X → E) =ᵐ[μ] 0 := by
      rw [hw_eq_zero]
      exact Lp.coeFn_zero E 2 μ
    filter_upwards [hw, hwzero] with x hwx hz hx
    have hxs : x ∈ s := hx
    have hsmul : inner ℂ (b i) (v x) • b i = 0 :=
      (hwx.trans (Set.indicator_of_mem hxs _)).symm.trans hz
    have hnorm : b i ≠ 0 := by
      intro hzero
      have := b.orthonormal.norm_eq_one i
      simp only [hzero, norm_zero, zero_ne_one] at this
    exact (smul_eq_zero.1 hsmul).resolve_right hnorm
  have hall : ∀ᵐ x ∂μ, ∀ (i : ι) (y : C), f i x = y.val → inner ℂ (b i) (v x) = 0 :=
    ae_all_iff.2 (fun i => ae_all_iff.2 (hfiber i))
  have hmemall : ∀ᵐ x ∂μ, ∀ i, f i x ∈ C := ae_all_iff.2 hmem
  apply Lp.ext
  filter_upwards [hmemall, hall, Lp.coeFn_zero E 2 μ] with x hx hall hz
  rw [hz]
  apply b.repr.injective
  ext i
  rw [b.repr_apply_apply, b.repr_apply_apply]
  change inner ℂ (b i) (v x) = inner ℂ (b i) 0
  rw [inner_zero_right]
  exact hall i ⟨f i x, hx i⟩ rfl

theorem topologicalClosure_iSup_jointEigenspace_eq_top_of_basis
    {ι J : Type*} [Countable ι] [Countable J] (b : HilbertBasis ι ℂ E)
    (f : ι → X → J → ℂ) (hf : ∀ i, Measurable (f i))
    {C : Set (J → ℂ)} (hC : C.Countable)
    (hmem : ∀ i, ∀ᵐ x ∂μ, f i x ∈ C)
    (T : J → Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (hT : ∀ (j : J) (v : Lp E 2 μ) i, ∀ᵐ x ∂μ,
      inner ℂ (b i) (T j v x) = f i x j * inner ℂ (b i) (v x)) :
    (⨆ y : C, ⨅ j : J, Module.End.eigenspace (T j).toLinearMap (y.val j)).topologicalClosure = ⊤ := by
  let : Countable C := hC.to_subtype
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro v hv
  have hfiber (i : ι) (y : C) :
      ∀ᵐ x ∂μ, f i x = y.val → inner ℂ (b i) (v x) = 0 := by
    let s : Set X := f i ⁻¹' {y.val}
    have hs : MeasurableSet s := hf i (measurableSet_singleton _)
    let P : E →L[ℂ] E := InnerProductSpace.rankOne ℂ (b i) (b i)
    have hvp : MemLp (fun x => inner ℂ (b i) (v x) • b i) 2 μ := P.comp_memLp v
    have hvi : MemLp (s.indicator (fun x => inner ℂ (b i) (v x) • b i)) 2 μ :=
      hvp.indicator hs
    let w : Lp E 2 μ :=
      MemLp.toLp (s.indicator (fun x => inner ℂ (b i) (v x) • b i)) hvi
    have hw : (w : X → E) =ᵐ[μ] s.indicator (fun x => inner ℂ (b i) (v x) • b i) :=
      hvi.coeFn_toLp
    have heigen : w ∈ ⨅ j : J, Module.End.eigenspace (T j).toLinearMap (y.val j) := by
      rw [Submodule.mem_iInf]
      intro j
      rw [Module.End.mem_eigenspace_iff]
      apply Lp.ext
      have hTall : ∀ᵐ x ∂μ, ∀ k, inner ℂ (b k) (T j w x) =
          f k x j * inner ℂ (b k) (w x) := ae_all_iff.2 (hT j w)
      filter_upwards [hTall, Lp.coeFn_smul (y.val j) w, hw] with x hTx hsx hwx
      change (T j w : X → E) x = (y.val j • w : Lp E 2 μ) x
      rw [hsx]
      apply b.repr.injective
      ext k
      rw [b.repr_apply_apply, b.repr_apply_apply, hTx k]
      change f k x j * inner ℂ (b k) (w x) = inner ℂ (b k) (y.val j • w x)
      rw [inner_smul_right]
      by_cases hx : x ∈ s
      · have hwv : w x = inner ℂ (b i) (v x) • b i :=
          hwx.trans (Set.indicator_of_mem hx _)
        by_cases hki : k = i
        · subst k
          have hxy : f i x = y.val := hx
          rw [hxy]
        · rw [hwv, inner_smul_right, b.orthonormal.inner_eq_zero hki]
          simp only [mul_zero]
      · have hw0 : w x = 0 := hwx.trans (Set.indicator_of_notMem hx _)
        simp only [hw0, inner_zero_right, mul_zero]
    have hinner : inner ℂ w v = 0 :=
      (Submodule.mem_orthogonal _ _).1 hv w (Submodule.mem_iSup_of_mem y heigen)
    have hself : inner ℂ w w = inner ℂ w v := by
      rw [L2.inner_def, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hw] with x hwx
      by_cases hx : x ∈ s
      · have hwv : w x = inner ℂ (b i) (v x) • b i :=
          hwx.trans (Set.indicator_of_mem hx _)
        rw [hwv, inner_smul_left, inner_smul_right, inner_smul_left]
        rw [inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
        norm_num
      · have hw0 : w x = 0 := hwx.trans (Set.indicator_of_notMem hx _)
        simp only [hw0, inner_zero_left]
    have hw_eq_zero : w = 0 := inner_self_eq_zero.1 (hself.trans hinner)
    have hwzero : (w : X → E) =ᵐ[μ] 0 := by
      rw [hw_eq_zero]
      exact Lp.coeFn_zero E 2 μ
    filter_upwards [hw, hwzero] with x hwx hz hx
    have hxs : x ∈ s := hx
    have hsmul : inner ℂ (b i) (v x) • b i = 0 :=
      (hwx.trans (Set.indicator_of_mem hxs _)).symm.trans hz
    have hnorm : b i ≠ 0 := by
      intro hzero
      have := b.orthonormal.norm_eq_one i
      simp only [hzero, norm_zero, zero_ne_one] at this
    exact (smul_eq_zero.1 hsmul).resolve_right hnorm
  have hall : ∀ᵐ x ∂μ, ∀ (i : ι) (y : C), f i x = y.val → inner ℂ (b i) (v x) = 0 :=
    ae_all_iff.2 (fun i => ae_all_iff.2 (hfiber i))
  have hmemall : ∀ᵐ x ∂μ, ∀ i, f i x ∈ C := ae_all_iff.2 hmem
  apply Lp.ext
  filter_upwards [hmemall, hall, Lp.coeFn_zero E 2 μ] with x hx hall hz
  rw [hz]
  apply b.repr.injective
  ext i
  rw [b.repr_apply_apply, b.repr_apply_apply]
  change inner ℂ (b i) (v x) = inner ℂ (b i) 0
  rw [inner_zero_right]
  exact hall i ⟨f i x, hx i⟩ rfl

theorem topologicalClosure_iSup_jointEigenspace_eq_top_of_sequence
    {ι J : Type*} [Countable ι] [Countable J]
    (f : ι → X → J → ℂ) (hf : ∀ i, Measurable (f i))
    {C : Set (J → ℂ)} (hC : C.Countable)
    (hmem : ∀ i, ∀ᵐ x ∂μ, f i x ∈ C)
    (T : J → Lp (lp (fun _ : ι => ℂ) 2) 2 μ →L[ℂ]
      Lp (lp (fun _ : ι => ℂ) 2) 2 μ)
    (hT : ∀ j (v : Lp (lp (fun _ : ι => ℂ) 2) 2 μ) i,
      ∀ᵐ x ∂μ, T j v x i = f i x j * v x i) :
    (⨆ y : C, ⨅ j : J, Module.End.eigenspace (T j).toLinearMap (y.val j)).topologicalClosure = ⊤ := by
  let b : HilbertBasis ι ℂ (lp (fun _ : ι => ℂ) 2) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hb (v : lp (fun _ : ι => ℂ) 2) (i : ι) : inner ℂ (b i) v = v i :=
    (b.repr_apply_apply v i).symm
  apply topologicalClosure_iSup_jointEigenspace_eq_top_of_basis b f hf hC hmem T
  intro j v i
  simpa only [hb] using hT j v i

theorem finite_orbit_family_dense_jointEigenspaces
    {J : Type*} [Finite J] (n : J → ℤ)
    (σ : ℤ → X → X) (hσ : ∀ k, MeasurePreserving (σ k) μ μ)
    (f : X → ℂ) (hf : Measurable f)
    (hcount : ∃ C : Set ℂ, C.Countable ∧ ∀ᵐ x ∂μ, f x ∈ C)
    (T : J → Lp (lp (fun _ : ℤ => ℂ) 2) 2 μ →L[ℂ]
      Lp (lp (fun _ : ℤ => ℂ) 2) 2 μ)
    (hT : ∀ j (v : Lp (lp (fun _ : ℤ => ℂ) 2) 2 μ) k,
      ∀ᵐ x ∂μ, T j v x k = f (σ (k - n j) x) * v x k) :
    ∃ C : Set (J → ℂ), C.Countable ∧
      (⨆ y : C, ⨅ j : J, Module.End.eigenspace (T j).toLinearMap (y.val j)).topologicalClosure = ⊤ := by
  obtain ⟨C, hC, hmem⟩ := hcount
  let R : Set (J → ℂ) := {g | ∀ j, g j ∈ C}
  have hR : R.Countable := Set.countable_pi (fun _ => hC)
  refine ⟨R, hR, ?_⟩
  apply topologicalClosure_iSup_jointEigenspace_eq_top_of_sequence
    (fun k x j => f (σ (k - n j) x)) _ hR _ T hT
  · intro k
    exact Measurable.of_eval (fun j => hf.comp (hσ (k - n j)).measurable)
  · intro k
    exact ae_all_iff.2 (fun j => (hσ (k - n j)).quasiMeasurePreserving.ae hmem)

theorem topologicalClosure_iSup_jointEigenspace_eq_top_of_sequence_real
    {ι J : Type*} [Countable ι] [Countable J]
    (f : ι → X → J → ℝ) (hf : ∀ i, Measurable (f i))
    {C : Set (J → ℝ)} (hC : C.Countable)
    (hmem : ∀ i, ∀ᵐ x ∂μ, f i x ∈ C)
    (T : J → Lp (lp (fun _ : ι => ℂ) 2) 2 μ →L[ℂ]
      Lp (lp (fun _ : ι => ℂ) 2) 2 μ)
    (hT : ∀ j (v : Lp (lp (fun _ : ι => ℂ) 2) 2 μ) i,
      ∀ᵐ x ∂μ, T j v x i = (f i x j : ℂ) * v x i) :
    (⨆ y : C, ⨅ j : J,
      Module.End.eigenspace (T j).toLinearMap (y.val j : ℂ)).topologicalClosure = ⊤ := by
  let e : (J → ℝ) → (J → ℂ) := fun r j => (r j : ℂ)
  let D : Set (J → ℂ) := e '' C
  have hD : D.Countable := hC.image e
  have hdense : (⨆ y : D, ⨅ j : J,
      Module.End.eigenspace (T j).toLinearMap (y.val j)).topologicalClosure = ⊤ := by
    apply topologicalClosure_iSup_jointEigenspace_eq_top_of_sequence
      (fun i x j => (f i x j : ℂ)) _ hD _ T hT
    · intro i
      exact Measurable.of_eval
        (fun j => ((measurable_pi_apply j).comp (hf i)).complex_ofReal)
    · intro i
      filter_upwards [hmem i] with x hx
      exact ⟨f i x, hx, rfl⟩
  apply top_le_iff.1
  rw [← hdense]
  apply Submodule.topologicalClosure_mono
  apply iSup_le
  intro y
  obtain ⟨r, hr, he⟩ := y.property
  have he' : y.val = e r := he.symm
  simpa only [he', e] using
    (le_iSup (fun z : C => ⨅ j : J,
      Module.End.eigenspace (T j).toLinearMap (z.val j : ℂ)) ⟨r, hr⟩)

theorem finite_orbit_family_dense_jointEigenspaces_real
    {J : Type*} [Finite J] (n : J → ℤ)
    (σ : ℤ → X → X) (hσ : ∀ k, MeasurePreserving (σ k) μ μ)
    (f : X → ℝ) (hf : Measurable f)
    (hcount : ∃ C : Set ℝ, C.Countable ∧ ∀ᵐ x ∂μ, f x ∈ C)
    (T : J → Lp (lp (fun _ : ℤ => ℂ) 2) 2 μ →L[ℂ]
      Lp (lp (fun _ : ℤ => ℂ) 2) 2 μ)
    (hT : ∀ j (v : Lp (lp (fun _ : ℤ => ℂ) 2) 2 μ) k,
      ∀ᵐ x ∂μ, T j v x k = (f (σ (k - n j) x) : ℂ) * v x k) :
    ∃ C : Set (J → ℝ), C.Countable ∧
      (⨆ y : C, ⨅ j : J,
        Module.End.eigenspace (T j).toLinearMap (y.val j : ℂ)).topologicalClosure = ⊤ := by
  obtain ⟨C, hC, hmem⟩ := hcount
  let R : Set (J → ℝ) := {g | ∀ j, g j ∈ C}
  have hR : R.Countable := Set.countable_pi (fun _ => hC)
  refine ⟨R, hR, ?_⟩
  apply topologicalClosure_iSup_jointEigenspace_eq_top_of_sequence_real
    (fun k x j => f (σ (k - n j) x)) _ hR _ T hT
  · intro k
    exact Measurable.of_eval (fun j => hf.comp (hσ (k - n j)).measurable)
  · intro k
    exact ae_all_iff.2 (fun j => (hσ (k - n j)).quasiMeasurePreserving.ae hmem)

end Invariant233.MultiplicationPurePoint

end OAI
