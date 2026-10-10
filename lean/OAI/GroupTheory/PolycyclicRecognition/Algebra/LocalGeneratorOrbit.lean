import OAI.GroupTheory.PolycyclicRecognition.Algebra.BilinearGeneratorOrbit

namespace OAI

/-! # Adjoint generators restricted to an open family of words

Only arbitrarily small prefixes are needed in the spanning proof. This lets
the conjugating words stay inside a specified open coordinate neighborhood.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Filter Module
open scoped Topology

variable {V I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem derivative_mem_submodule_of_eventually
    {f : ℝ → V} {v : V} (hd : HasDerivAt f v 0) (P : Submodule ℝ V)
    (hf : ∀ᶠ t in 𝓝 0, f t ∈ P) : v ∈ P := by
  have hzero : f 0 ∈ P :=
    (show (0 : ℝ) ∈ {t : ℝ | f t ∈ P} from mem_of_mem_nhds hf)
  apply P.closed_of_finiteDimensional.mem_of_tendsto hd.tendsto_slope
  filter_upwards [hf.filter_mono nhdsWithin_le_nhds] with t ht
  exact P.smul_mem _ (P.sub_mem ht hzero)

def localBilinearOrbitSpan (B : V →L[ℝ] V →L[ℝ] V) (X : I → V)
    (good : List (I × ℝ) → Prop) : Submodule ℝ V :=
  Submodule.span ℝ {v | ∃ w, good w ∧ ∃ i, bilinearAdjointWord B X w (X i) = v}

omit [FiniteDimensional ℝ V] in
theorem local_bilinear_generator_mem (B : V →L[ℝ] V →L[ℝ] V) (X : I → V)
    (good : List (I × ℝ) → Prop) (hnil : good []) (i : I) :
    X i ∈ localBilinearOrbitSpan B X good := by
  apply Submodule.subset_span
  exact ⟨[], hnil, i, by simp [bilinearAdjointWord]⟩

theorem local_bilinear_ad_mem (B : V →L[ℝ] V →L[ℝ] V) (X : I → V)
    (good : List (I × ℝ) → Prop)
    (hprefix : ∀ w, good w → ∀ i, ∀ᶠ t in 𝓝 (0 : ℝ), good ((i, t) :: w))
    (i : I) {v : V} (hv : v ∈ localBilinearOrbitSpan B X good) :
    B (X i) v ∈ localBilinearOrbitSpan B X good := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨w, hw, j, rfl⟩ := hv
    let z := bilinearAdjointWord B X w (X j)
    have hd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • B (X i)) z)
        (B (X i) z) 0 := by
      simpa using (hasDerivAt_exp_smul_const (B (X i)) (0 : ℝ)).clm_apply
        (hasDerivAt_const (0 : ℝ) z)
    apply derivative_mem_submodule_of_eventually hd
    filter_upwards [hprefix w hw i] with t ht
    apply Submodule.subset_span
    exact ⟨(i, t) :: w, ht, j, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => simpa using (localBilinearOrbitSpan B X good).add_mem hx hy
  | smul c x _ hx => simpa using (localBilinearOrbitSpan B X good).smul_mem c hx

theorem localBilinearOrbitSpan_eq_top {J : Type*}
    (B : V →L[ℝ] V →L[ℝ] V) (hB : IsLieBracket B)
    (X : I → V) (b : Basis J ℝ V) (w : J → FreeMagma I)
    (hw : ∀ j, evalBilinearWord B X (w j) = b j)
    (good : List (I × ℝ) → Prop) (hnil : good [])
    (hprefix : ∀ w, good w → ∀ i, ∀ᶠ t in 𝓝 (0 : ℝ), good ((i, t) :: w)) :
    localBilinearOrbitSpan B X good = ⊤ := by
  let := lieRingOfBilinear B hB
  let := lieAlgebraOfBilinear B hB
  have hX := lieSpan_eq_top_of_word_basis B hB X b w hw
  let P := localBilinearOrbitSpan B X good
  have hstab : submoduleAdjointStabilizer P = ⊤ := by
    apply top_unique
    rw [← hX]
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨i, rfl⟩ v hv
    exact local_bilinear_ad_mem B X good hprefix i hv
  let Q : LieSubalgebra ℝ V := { P with
    lie_mem' := by
      intro x y hx hy
      have hx' : x ∈ submoduleAdjointStabilizer P := by rw [hstab]; trivial
      exact hx' y hy }
  have hQ : Q = ⊤ := by
    apply top_unique
    rw [← hX]
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨i, rfl⟩
    exact local_bilinear_generator_mem B X good hnil i
  exact congrArg LieSubalgebra.toSubmodule hQ

theorem exists_local_bilinearOrbit_basis {J : Type*}
    (B : V →L[ℝ] V →L[ℝ] V) (hB : IsLieBracket B)
    (X : I → V) (b₀ : Basis J ℝ V) (w₀ : J → FreeMagma I)
    (hw₀ : ∀ j, evalBilinearWord B X (w₀ j) = b₀ j)
    (good : List (I × ℝ) → Prop) (hnil : good [])
    (hprefix : ∀ w, good w → ∀ i, ∀ᶠ t in 𝓝 (0 : ℝ), good ((i, t) :: w)) :
    ∃ (b : Basis (Fin (finrank ℝ V)) ℝ V)
      (w : Fin (finrank ℝ V) → List (I × ℝ)) (i : Fin (finrank ℝ V) → I),
      ∀ k, good (w k) ∧ bilinearAdjointWord B X (w k) (X (i k)) = b k := by
  classical
  let S : Set V := {v | ∃ w, good w ∧ ∃ i, bilinearAdjointWord B X w (X i) = v}
  have hspan : ⊤ ≤ Submodule.span ℝ S :=
    (localBilinearOrbitSpan_eq_top B hB X b₀ w₀ hw₀ good hnil hprefix).ge
  let J' := (linearIndepOn_empty ℝ (id : V → V)).extend (Set.empty_subset S)
  let b : Basis J' ℝ V := Basis.ofSpan hspan
  let : Fintype J' := Fintype.ofFinite _
  let e : J' ≃ Fin (finrank ℝ V) :=
    Fintype.equivFinOfCardEq (finrank_eq_card_basis b).symm
  have hb (k : Fin (finrank ℝ V)) :
      ∃ w, good w ∧ ∃ i, bilinearAdjointWord B X w (X i) = (b.reindex e) k := by
    have hmem : b (e.symm k) ∈ S :=
      Basis.ofSpan_subset hspan (show b (e.symm k) ∈ range b from ⟨_, rfl⟩)
    simpa only [S, mem_ofPred_eq, Basis.coe_reindex, Function.comp_apply] using hmem
  choose w hw i hi using hb
  exact ⟨b.reindex e, w, i, fun k => ⟨hw k, hi k⟩⟩

end PolycyclicRecognition

end

end OAI
