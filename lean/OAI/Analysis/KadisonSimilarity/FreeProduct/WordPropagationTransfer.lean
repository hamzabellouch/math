import OAI.Analysis.KadisonSimilarity.FreeProduct.WordLevelRepeatedOperators
import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeCornerEndgame

namespace OAI

/-! Transfer the multiplicity propagation estimate to the actual orthogonal
word columns used by the finite Fourier test. -/

noncomputable section
namespace KadisonSimilarity

universe u
variable {E F : Type u} {K H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {J : ℕ → Type*} [∀ n, NormedAddCommGroup (J n)]
  [∀ n, InnerProductSpace ℂ (J n)] [∀ n, CompleteSpace (J n)]

variable (U : OrthogonalWordLevels (MultiplicityWordSpace J E F) H)

/-- The concrete column at a fixed word degree, endpoint, and repeated letter. -/
def repeatedWordInclusion (n : ℕ) (R : K →ₗᵢ[ℂ] J n)
    (d : E) (r : F) (hd : ‖d‖ = 1) (hr : ‖r‖ = 1) : K →ₗᵢ[ℂ] H where
  toLinearMap := (U.inclusion n).toLinearMap.comp
    ((hilbertTensorRightInsert (endpointWord d (fun _ : Fin n => r))).toLinearMap.comp
      R.toLinearMap)
  norm_map' x := by
    change ‖U.inclusion n (hilbertTensorInsert (R x)
      (endpointWord d (fun _ : Fin n => r)))‖ = ‖x‖
    rw [LinearIsometry.norm_map, norm_hilbertTensorInsert, LinearIsometry.norm_map,
      norm_endpointWord_constant d r hd hr, mul_one]

omit [CompleteSpace H] [CompleteSpace K] [∀ n, CompleteSpace (J n)] in
@[simp] theorem repeatedWordInclusion_apply (n : ℕ) (R : K →ₗᵢ[ℂ] J n)
    (d : E) (r : F) (hd : ‖d‖ = 1) (hr : ‖r‖ = 1) (x : K) :
    repeatedWordInclusion U n R d r hd hr x = U.inclusion n
      (hilbertTensorInsert (R x) (endpointWord d (fun _ : Fin n => r))) := rfl

omit [CompleteSpace H] [CompleteSpace K] [∀ n, CompleteSpace (J n)] in
/-- A multiplicity error has exactly the same norm in a normalized word
column. This supplies the full-output error needed in the Hankel test. -/
theorem norm_repeatedWordInclusion_error_le (n : ℕ) (R : K →ₗᵢ[ℂ] J n)
    (d : E) (r : F) (hd : ‖d‖ = 1) (hr : ‖r‖ = 1)
    (Y : H →L[ℂ] H) (B : K →L[ℂ] K) (Bn : J n →L[ℂ] J n)
    (hY : ∀ v, Y (U.inclusion n (hilbertTensorInsert v
        (endpointWord d (fun _ : Fin n => r)))) =
      U.inclusion n (hilbertTensorInsert (Bn v)
        (endpointWord d (fun _ : Fin n => r))))
    {η : ℝ} (hη : 0 ≤ η)
    (hprop : ∀ x, ‖Bn (R x) - R (B x)‖ ≤ η * ‖x‖) :
    ‖Y.comp (repeatedWordInclusion U n R d r hd hr).toContinuousLinearMap -
      (repeatedWordInclusion U n R d r hd hr).toContinuousLinearMap.comp B‖ ≤ η := by
  apply ContinuousLinearMap.opNorm_le_bound _ hη
  intro x
  change ‖Y (U.inclusion n (hilbertTensorInsert (R x)
      (endpointWord d (fun _ : Fin n => r)))) -
    U.inclusion n (hilbertTensorInsert (R (B x))
      (endpointWord d (fun _ : Fin n => r)))‖ ≤ _
  rw [hY, ← map_sub, LinearIsometry.norm_map]
  change ‖hilbertTensorRightInsert (endpointWord d (fun _ : Fin n => r)) (Bn (R x)) -
    hilbertTensorRightInsert (endpointWord d (fun _ : Fin n => r)) (R (B x))‖ ≤ _
  rw [← map_sub, hilbertTensorRightInsert_apply, norm_hilbertTensorInsert,
    norm_endpointWord_constant d r hd hr, mul_one]
  exact hprop x

omit [CompleteSpace H] [CompleteSpace K] [∀ n, CompleteSpace (J n)] in
/-- Word columns at different degrees are orthogonal. -/
theorem repeatedWordInclusion_orthogonal (n m : ℕ) (hnm : n ≠ m)
    (Rn : K →ₗᵢ[ℂ] J n) (Rm : K →ₗᵢ[ℂ] J m)
    (d : E) (r : F) (hd : ‖d‖ = 1) (hr : ‖r‖ = 1) (x y : K) :
    inner ℂ (repeatedWordInclusion U n Rn d r hd hr x)
      (repeatedWordInclusion U m Rm d r hd hr y) = 0 :=
  U.orthogonal n m hnm _ _

/-- The finite Fourier test consumes the derived multiplicity propagation
bounds, with the orthogonality and full-column errors constructed here. -/
theorem free_corner_from_multiplicity_propagation
    {N : ℕ} (hN : 0 < N) (R : ∀ n, K →ₗᵢ[ℂ] J n)
    (d : E) (r : F) (hd : ‖d‖ = 1) (hr : ‖r‖ = 1)
    (Y T : H →L[ℂ] H) (B S : K →L[ℂ] K) (Bn : ∀ n, J n →L[ℂ] J n)
    (hY : ∀ n v, Y (U.inclusion n (hilbertTensorInsert v
        (endpointWord d (fun _ : Fin n => r)))) =
      U.inclusion n (hilbertTensorInsert (Bn n v)
        (endpointWord d (fun _ : Fin n => r))))
    (hYstar : ∀ n v, Y.adjoint (U.inclusion n (hilbertTensorInsert v
        (endpointWord d (fun _ : Fin n => r)))) =
      U.inclusion n (hilbertTensorInsert ((Bn n).adjoint v)
        (endpointWord d (fun _ : Fin n => r))))
    (hlevel : ∀ n x, Y (U.inclusion n x) ∈ (U.inclusion n).toLinearMap.range)
    (hlevelstar : ∀ n x, Y.adjoint (U.inclusion n x) ∈ (U.inclusion n).toLinearMap.range)
    (toeplitz : Matrix (Fin N) (Fin N) ℝ)
    {u ε c₀ : ℝ} (hu : 0 < u) (hε : 0 ≤ ε) (hc₀ : 0 ≤ c₀)
    (hT : ‖T‖ ≤ 3 * u) (hcomm : ‖commutator Y T‖ ≤ ε * ‖T‖)
    (hprop : ∀ n x, ‖Bn n (R n x) - R n (B x)‖ ≤ 2 * c₀ * ε * ‖x‖)
    (hpropstar : ∀ n x, ‖(Bn n).adjoint (R n x) - R n (B.adjoint x)‖ ≤
      2 * c₀ * ε * ‖x‖)
    (hfourier :
      let V : Fin N → K →L[ℂ] H := fun i =>
        (repeatedWordInclusion U i.val (R i.val) d r hd hr).toContinuousLinearMap
      (sumColumns V).adjoint.comp (T.comp (sumColumns V)) =
        (u : ℂ) • matrixOperator (fun i j =>
          (toeplitz i j : ℂ) • ContinuousLinearMap.id ℂ K +
            (arcHankelMatrix N i j : ℂ) • S)) :
    ‖commutator B S‖ ≤ 6 * Real.pi ^ 2 * (1 + 4 * c₀) * ε := by
  let V : Fin N → K →L[ℂ] H := fun i =>
    (repeatedWordInclusion U i.val (R i.val) d r hd hr).toContinuousLinearMap
  let L : Fin N → Submodule ℂ H := fun i => (U.inclusion i.val).toLinearMap.range
  have hnorm (i : Fin N) : ‖V i‖ ≤ 1 :=
    (repeatedWordInclusion U i.val (R i.val) d r hd hr).norm_toContinuousLinearMap_le
  have hmem (i : Fin N) (x : K) : V i x ∈ L i := ⟨_, rfl⟩
  have horth (i j : Fin N) (hij : i ≠ j) (x : H) (hx : x ∈ L i)
      (y : H) (hy : y ∈ L j) : inner ℂ x y = 0 := by
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact U.orthogonal i.val j.val (fun h => hij (Fin.ext h)) a b
  apply free_corner_bound_of_word_levels hN Y T B S V L hnorm hmem horth
    (fun i x hx => by obtain ⟨a, rfl⟩ := hx; exact hlevel i.val a)
    (fun i x hx => by obtain ⟨a, rfl⟩ := hx; exact hlevelstar i.val a)
    toeplitz hu hε hc₀ hT hcomm
  · intro i
    exact norm_repeatedWordInclusion_error_le U i.val (R i.val) d r hd hr Y B
      (Bn i.val) (hY i.val) (by positivity) (hprop i.val)
  · intro i
    exact norm_repeatedWordInclusion_error_le U i.val (R i.val) d r hd hr Y.adjoint B.adjoint
      (Bn i.val).adjoint (hYstar i.val) (by positivity) (hpropstar i.val)
  · exact hfourier

end KadisonSimilarity

end

end OAI
