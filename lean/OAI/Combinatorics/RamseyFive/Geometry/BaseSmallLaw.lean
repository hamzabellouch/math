import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.DimensionTwo
import OAI.Combinatorics.RamseyFive.Geometry.BaseCapturedLaw

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence FiniteEntropy SubsetEncoding MeasureTheory
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
theorem baseSmallLaw (S U : Finset (ℙ K V)) (hSU : S⊆U) (P τ : ℝ)
    (hP : 1≤P) (hn : (S.card:ℝ)≤100*(Nat.card K:ℝ)*P) (R : ℕ) (L₀ : ℝ≥0) :
    baseCaptureLaw S U P τ R L₀ none≤0 ∧
    Real.log (Fintype.card (baseAlphabet U S.card P τ):ℝ)≤
      100*(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+P) := by
  refine ⟨?_,?_⟩
  · apply baseCaptureLaw_failure S U P τ R L₀ Set.univ 0 (by simp)
    intro t _
    let n : Fin (Fintype.card (ℙ K V)+1) := ⟨S.card,Nat.lt_succ_of_le (Finset.card_le_univ S)⟩
    let m : baseAlphabet U S.card P τ := by
      simpa only [baseAlphabet,hn,ite_true] using encode S U hSU
    refine ⟨m,?_⟩
    have hd := baseDecoded_small U S.card P τ L₀ (t n) hn (encode S U hSU)
    change (baseDecoded U S.card P τ L₀ (t n) m)⊆U ∧
      ((baseDecoded U S.card P τ L₀ (t n) m).card:ℝ)≤(S.card:ℝ)*Real.exp (2*P) ∧
      (9/10:ℝ)*S.card≤((baseDecoded U S.card P τ L₀ (t n) m∩S).card:ℝ)
    rw [hd,decode_encode S U hSU,Finset.inter_self]
    refine ⟨hSU,?_,?_⟩
    · exact le_mul_of_one_le_right (by positivity) (Real.one_le_exp_iff.mpr (by linarith))
    · nlinarith only [show (0:ℝ)≤S.card by positivity]
  · rw [baseAlphabet_small_card U S.card P τ hn]
    have hc := (small_set_description S U hSU (Nat.card K) P hn).2
    exact hc.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
end

open Module ProjectiveIncidence FiniteEntropy Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology

theorem eventually_two_law {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [∀x : ℙ K V,Fintype (RadialLine x)],
    ∀ (S U : Finset (ℙ K V)) (T : Finset (ℙ K (Dual K V))),
      finrank K V=3 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-200*beta η) → S.Nonempty → S⊆U → S.card≤T.card →
      (Nat.card K:ℝ)*(incidences S T:ℝ)≤τ*S.card*T.card →
      (Nat.card K:ℝ)^3*Real.exp (-b)≤(S.card:ℝ)*T.card →
      baseCaptureLaw S U (P η σ D R) τ R L₀ none≤Real.exp (-(Nat.card K:ℝ)) := by
  filter_upwards [eventually_two_complete_predictor hη hη' Cb hCb] with σ hh
  intro D b τ R L₀ K V _ _ _ _ _ _ _ _ S U T hdim hq hr hL hb hbhi hτ hτhi hS hSU hST hdens hprod
  obtain ⟨_,E,hE,hs⟩ := hh D b τ R L₀ K V S U T hdim hq hr hL hb hbhi hτ hτhi hS hSU hST hdens hprod
  exact baseCaptureLaw_failure S U _ τ R L₀ E _ hE hs

end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ProjectiveIncidence

section
open Module
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

lemma incident_mk_pair (v : V) (hv : v≠0) (a : Dual K V) (ha : a≠0) :
    Incident (Projectivization.mk K v hv) (Projectivization.mk K a ha) ↔ a v=0 := by
  rw [incident_mk_right]
  obtain ⟨c,hc⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
  rw [←hc]
  simp only [LinearMap.map_smul_of_tower,Units.smul_def,smul_eq_mul,mul_eq_zero,Units.ne_zero,false_or]

lemma incident_coordinates (e : V≃ₗ[K]W) (x : ℙ K V) (f : ℙ K (Dual K V)) :
    Incident (projectiveEquiv e x) (projectiveEquiv e.symm.dualMap f) ↔ Incident x f := by
  induction x using Projectivization.ind with | h v hv =>
  induction f using Projectivization.ind with | h a ha =>
  change Incident (Projectivization.map e.toLinearMap e.injective (Projectivization.mk K v hv))
    (Projectivization.map e.symm.dualMap.toLinearMap e.symm.dualMap.injective (Projectivization.mk K a ha)) ↔ _
  rw [Projectivization.map_mk,Projectivization.map_mk,incident_mk_pair,incident_mk_pair]
  simp only [LinearEquiv.coe_coe,LinearEquiv.dualMap_apply,LinearEquiv.symm_apply_apply]

lemma incidences_coordinates (e : V≃ₗ[K]W) (S : Finset (ℙ K V)) (T : Finset (ℙ K (Dual K V))) :
    incidences (S.map (projectiveEquiv e).toEmbedding)
      (T.map (projectiveEquiv e.symm.dualMap).toEmbedding)=incidences S T := by
  have hh : (incidences (S.map (projectiveEquiv e).toEmbedding)
      (T.map (projectiveEquiv e.symm.dualMap).toEmbedding):ℝ)=(incidences S T:ℝ) := by
    rw [incidences_eq_sum,incidences_eq_sum]
    simp only [Finset.sum_map,Equiv.toEmbedding_apply,incidenceEntry,incident_coordinates]
  exact_mod_cast hh

lemma decoded_coordinates (e : V≃ₗ[K]W) (U S : Finset (ℙ K V)) (Z : Finset (ℙ K W))
    (hZU : Z⊆U.map (projectiveEquiv e).toEmbedding) :
    let W₀ := Z.map (projectiveEquiv e).symm.toEmbedding
    W₀⊆U ∧ W₀.card=Z.card ∧ (W₀∩S).card=(Z∩S.map (projectiveEquiv e).toEmbedding).card := by
  dsimp only
  refine ⟨?_,Finset.card_map _,?_⟩
  · intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y,hy,he⟩ := Finset.mem_map.mp (hZU hz)
    simpa only [←he,Equiv.toEmbedding_apply,Equiv.symm_apply_apply] using hy
  · have he : S=(S.map (projectiveEquiv e).toEmbedding).map (projectiveEquiv e).symm.toEmbedding := by
      ext x
      simp only [Finset.mem_map,Equiv.toEmbedding_apply]
      constructor
      · intro hx
        exact ⟨projectiveEquiv e x,⟨x,hx,rfl⟩,(projectiveEquiv e).symm_apply_apply x⟩
      · rintro ⟨_,⟨y,hy,rfl⟩,rfl⟩
        simpa only [Equiv.symm_apply_apply] using hy
    conv_lhs => rw [he]
    rw [←Finset.map_inter,Finset.card_map]

end

open Module
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

noncomputable def bidualPoint : (ℙ K V) ≃ (ℙ K (Dual K (Dual K V))) :=
  projectiveEquiv (Module.evalEquiv K V)

lemma incident_bidual (x : ℙ K V) (f : ℙ K (Dual K V)) :
    Incident f (bidualPoint x) ↔ Incident x f := by
  induction x using Projectivization.ind with | h v hv =>
  induction f using Projectivization.ind with | h a ha =>
  change Incident (Projectivization.mk K a ha)
    (Projectivization.map (Module.evalEquiv K V).toLinearMap (Module.evalEquiv K V).injective
      (Projectivization.mk K v hv)) ↔ _
  rw [Projectivization.map_mk,incident_mk_pair,incident_mk_pair]
  rfl

lemma incidences_bidual (S : Finset (ℙ K V)) (T : Finset (ℙ K (Dual K V))) :
    incidences T (S.map bidualPoint.toEmbedding)=incidences S T := by
  have hh : (incidences T (S.map bidualPoint.toEmbedding):ℝ)=(incidences S T:ℝ) := by
    rw [incidences_eq_sum,incidences_eq_sum,Finset.sum_comm]
    simp only [Finset.sum_map,Equiv.toEmbedding_apply,incidenceEntry,incident_bidual]
  exact_mod_cast hh

end SharpRamseyFive.ProjectiveIncidence

end OAI
