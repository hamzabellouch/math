import OAI.Dynamics.EntropyCounterexample.SkewProduct

namespace OAI

noncomputable section

open scoped OnePoint

namespace Problem340.RawInvariantSets

def zeroSlice {q : ℕ} (t₀ : AddCircle (100 : ℝ))
    (v : Fin q → OnePoint ℂ) : RawState q :=
  (t₀, ((0 : ℂ) : OnePoint ℂ), v)

def registerMap {q : ℕ} (T : OnePoint ℂ → ℂ)
    (v : Fin q → OnePoint ℂ) : Fin q → OnePoint ℂ :=
  fun i => (T (v i) : OnePoint ℂ)

@[continuity, fun_prop]
theorem continuous_zeroSlice {q : ℕ} (t₀ : AddCircle (100 : ℝ)) :
    Continuous (@zeroSlice q t₀) := by
  exact continuous_const.prodMk (continuous_const.prodMk continuous_id)

theorem zeroSlice_injective {q : ℕ} (t₀ : AddCircle (100 : ℝ)) :
    Function.Injective (@zeroSlice q t₀) := by
  intro v w h
  exact congrArg (fun x : RawState q => x.2.2) h

theorem semiconj_zeroSlice {q : ℕ}
    (h : RawState q → ℝ) (C : RawState q → ℂ)
    (R : RawState q → Fin q → ℂ) (t₀ : AddCircle (100 : ℝ))
    (T : OnePoint ℂ → ℂ)
    (hh : ∀ v, h (zeroSlice t₀ v) = 0)
    (hC : ∀ v, C (zeroSlice t₀ v) = 0)
    (hR : ∀ v i, R (zeroSlice t₀ v) i = T (v i)) :
    Function.Semiconj (zeroSlice t₀) (registerMap T) (rawUpdate h C R) := by
  intro v
  have hRv : R (zeroSlice t₀ v) = fun i => T (v i) := funext (hR v)
  unfold rawUpdate
  rw [hh v, hC v, hRv]
  simp [zeroSlice, rawQuadratic]
  rfl

def zeroSet (q : ℕ) (t₀ : AddCircle (100 : ℝ)) : Set (RawState q) :=
  Set.range (zeroSlice t₀)

theorem isCompact_zeroSet (q : ℕ) (t₀ : AddCircle (100 : ℝ)) :
    IsCompact (zeroSet q t₀) :=
  isCompact_range (continuous_zeroSlice t₀)

theorem zeroSet_nonempty (q : ℕ) (t₀ : AddCircle (100 : ℝ)) :
    (zeroSet q t₀).Nonempty := Set.range_nonempty _

theorem mem_zeroSet_iff {q : ℕ} (t₀ : AddCircle (100 : ℝ)) (x : RawState q) :
    x ∈ zeroSet q t₀ ↔ x.1 = t₀ ∧ x.2.1 = ((0 : ℂ) : OnePoint ℂ) := by
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨rfl, rfl⟩
  · rintro ⟨ht, hz⟩
    exact ⟨x.2.2, Prod.ext ht.symm (Prod.ext hz.symm rfl)⟩

theorem mapsTo_zeroSet {q : ℕ}
    (h : RawState q → ℝ) (C : RawState q → ℂ)
    (R : RawState q → Fin q → ℂ) (t₀ : AddCircle (100 : ℝ))
    (T : OnePoint ℂ → ℂ)
    (hh : ∀ v, h (zeroSlice t₀ v) = 0)
    (hC : ∀ v, C (zeroSlice t₀ v) = 0)
    (hR : ∀ v i, R (zeroSlice t₀ v) i = T (v i)) :
    Set.MapsTo (rawUpdate h C R) (zeroSet q t₀) (zeroSet q t₀) := by
  rintro x ⟨v, rfl⟩
  exact ⟨registerMap T v, semiconj_zeroSlice h C R t₀ T hh hC hR v⟩

def registerParam {q : ℕ} {S : Type*} (e : S → OnePoint ℂ)
    (v : Fin q → S) : Fin q → OnePoint ℂ := fun i => e (v i)

theorem continuous_registerParam {q : ℕ} {S : Type*} [TopologicalSpace S]
    {e : S → OnePoint ℂ} (he : Continuous e) :
    Continuous (@registerParam q S e) :=
  continuous_pi fun i => he.comp (continuous_apply i)

theorem registerParam_surjective {q : ℕ} {S : Type*}
    {e : S → OnePoint ℂ} (he : Function.Surjective e) :
    Function.Surjective (@registerParam q S e) := by
  intro v
  choose w hw using fun i => he (v i)
  exact ⟨w, funext hw⟩

theorem semiconj_registerParam {q : ℕ} {S : Type*}
    (e : S → OnePoint ℂ) (A : S → S) (T : OnePoint ℂ → ℂ)
    (he : ∀ x, e (A x) = (T (e x) : OnePoint ℂ)) :
    Function.Semiconj (@registerParam q S e) (fun v i => A (v i)) (registerMap T) := by
  intro v
  funext i
  exact he (v i)

theorem coverEntropy_realized_zeroSet
    {q : ℕ} {S X : Type*} [UniformSpace S] [CompactSpace S] [Nonempty S]
    [UniformSpace X]
    (h : RawState q → ℝ) (C : RawState q → ℂ)
    (R : RawState q → Fin q → ℂ) (t₀ : AddCircle (100 : ℝ))
    (T : OnePoint ℂ → ℂ)
    (hh : ∀ v, h (zeroSlice t₀ v) = 0)
    (hC : ∀ v, C (zeroSlice t₀ v) = 0)
    (hR : ∀ v i, R (zeroSlice t₀ v) i = T (v i))
    (e : S ≃ₜ OnePoint ℂ) (A : S → S)
    (he : ∀ x, e (A x) = (T (e x) : OnePoint ℂ))
    (hentropy : Dynamics.coverEntropy (fun v : Fin q → S => fun i => A (v i))
      (Set.univ : Set (Fin q → S)) = 0)
    (φ : RawState q → X) (hφ : Continuous φ) (G : X → X)
    (hG : Function.Semiconj φ (rawUpdate h C R) G) :
    Dynamics.coverEntropy G (φ '' zeroSet q t₀) = 0 := by
  let ψ : (Fin q → S) → X := φ ∘ zeroSlice t₀ ∘ registerParam e
  have hψ : Continuous ψ :=
    hφ.comp ((continuous_zeroSlice t₀).comp (continuous_registerParam e.continuous))
  have hs : Function.Semiconj ψ (fun v i => A (v i)) G := by
    intro v
    change φ (zeroSlice t₀ (registerParam e (fun i => A (v i)))) =
      G (φ (zeroSlice t₀ (registerParam e v)))
    rw [semiconj_registerParam e A T he v,
      semiconj_zeroSlice h C R t₀ T hh hC hR (registerParam e v), hG]
  have hrange : Set.range ψ = φ '' zeroSet q t₀ := by
    rw [show ψ = φ ∘ (zeroSlice t₀ ∘ registerParam e) from rfl,
      Set.range_comp, Set.range_comp,
      Set.range_eq_univ.mpr (registerParam_surjective e.surjective), Set.image_univ]
    rfl
  rw [← hrange]
  apply le_antisymm _ (Dynamics.coverEntropy_nonneg G (Set.range_nonempty ψ))
  have hb := Dynamics.coverEntropy_image_le_of_uniformContinuous hs
    (CompactSpace.uniformContinuous_of_continuous hψ) Set.univ
  simpa only [Set.image_univ, hentropy] using hb

end Problem340.RawInvariantSets

end

end OAI
