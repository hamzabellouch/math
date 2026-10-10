import OAI.Dynamics.ThreeTorus.FiniteBlocks
import OAI.Dynamics.ThreeTorus.Prediction

namespace OAI

/-! Repeated blocks, prediction budgets, physical Laurent polynomials, and actual cyclic approximation. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

/-- A finite trace of actual centered blocks. `A` is exactly the sum of their
estimators. This data retains each anchor and each physical passage. -/
inductive ActualColoredBlocks {m : ℕ} (C : ColoredState (Fin m)) :
    ColoredState (Fin m) → ℕ → Equiv.Perm TripleTorus → (UnitAddCircle → ℂ) → Prop
  | nil : ActualColoredBlocks C C 0 (Equiv.refl _) (fun _ => 0)
  | snoc {E F : ColoredState (Fin m)} {k : ℕ} {α β : Equiv.Perm TripleTorus}
      {A D : UnitAddCircle → ℂ} (h : ActualColoredBlocks C E k α A)
      (hb : ActualColoredBlock E F β D) :
      ActualColoredBlocks C F (k+1) (α.trans β) (fun z => A z+D z)

namespace ActualColoredBlocks
variable {m : ℕ} {C E : ColoredState (Fin m)} {k : ℕ} {α : Equiv.Perm TripleTorus}
    {A : UnitAddCircle → ℂ} (h : ActualColoredBlocks C E k α A)
include h
lemma continuous : Continuous α := by
  induction h with
  | nil => exact continuous_id
  | snoc h hb ih => exact hb.continuous.comp ih
lemma preserves : MeasurePreserving α tripleVolume tripleVolume := by
  induction h with
  | nil => exact MeasurePreserving.id _
  | snoc h hb ih => exact hb.preserves.comp ih
lemma physicalError_eq (f g : TripleTorus → ℂ) :
    physicalError (f ∘ α) (g ∘ α) = physicalError f g := by
  induction h generalizing f g with
  | nil => rfl
  | @snoc E F k α β A D h hb ih =>
    change physicalError ((f ∘ β) ∘ α) ((g ∘ β) ∘ α) = _
    rw [ih,hb.physicalError_eq]
lemma estimator_continuous : Continuous A := by
  induction h with
  | nil => exact continuous_const
  | snoc _ hb ih => exact ih.add hb.estimator_continuous
lemma estimator_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun x : ℝ => A (x:UnitAddCircle)) := by
  induction h with
  | nil => exact contDiff_const
  | snoc _ hb ih => exact ih.add hb.estimator_smooth
lemma estimator_reflection (z : UnitAddCircle) : A (-z) = conj (A z) := by
  induction h with
  | nil => simp
  | snoc _ hb ih => simp only [ih,hb.estimator_reflection,map_add]
end ActualColoredBlocks

lemma integral_blockPreviousError_eq {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hc : ∀ r, Continuous (p r)) (b : Fin m → ℂ) {A : UnitAddCircle → ℂ}
    (hA : Continuous A) (k : ℕ) :
    (∫ z, blockPreviousError p b A k z ∂phaseHaar) =
      ∑ r, ∫ z, p r z*‖A z-(k:ℂ)*b r‖^2 ∂phaseHaar := by
  apply integral_finsetSum
  intro r _
  exact continuous_circle_integrable ((hc r).mul ((hA.sub continuous_const).norm.pow 2))

lemma block_increment_budget {δ : ℝ} (hd : 0 < δ) (hd1 : δ ≤ 1/100) :
    4/δ+δ^2 ≤ 5/δ := by
  have hd' : δ ≤ 1 := by linarith
  have hs : δ^2 ≤ 1 := by nlinarith
  have hi : 1 ≤ 1/δ := (le_div_iff₀ hd).2 (by simpa using hd')
  simp only [div_eq_mul_inv] at *
  linarith

/-- Source04's repeated blocks, with every new center formed from the actual
current densities. Physical transport, not a spectral model, keeps the mass
strictly below two. No future uniform strength bound is required. -/
theorem actual_repeated_blocks {m : ℕ} (C : ColoredState (Fin m))
    (τR : Fin m → Fin m) (hτR : Involutive τR) (hrC : C.Reflection τR)
    (tags : Fin m → ℂ) (htags : ∀ r, ‖tags r‖ ≤ 1)
    (htrR : ∀ r, tags (τR r) = conj (tags r))
    {delta ε κ : ℝ} (hd : 0 < delta) (hd1 : delta ≤ 1/100) (hε : 0 < ε) (hκ : 0 < κ)
    (hmass : (∫ z, blockTotal C.density z ∂phaseHaar) < 2) (K : ℕ) :
    ∃ E : ColoredState (Fin m), ∃ α : Equiv.Perm TripleTorus, ∃ A : UnitAddCircle → ℂ,
      ActualColoredBlocks C E K α A ∧
      (∀ r, physicalError (C.vector r) (E.vector r ∘ α) < ε) ∧
      ((∫ z, Real.sqrt (blockTotal C.density z) ∂phaseHaar)-400*(K:ℝ)*delta^2 ≤
        ∫ z, Real.sqrt (blockTotal E.density z) ∂phaseHaar) ∧
      ((∫ z, blockPreviousError E.density tags A K z ∂phaseHaar) ≤ (K:ℝ)*(5/delta)) ∧
      (∫ z, blockTotal E.density z ∂phaseHaar) < 2 ∧ E.Reflection τR ∧
      (0 < K → ∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ E.packets.GoodArc δ) := by
  induction K generalizing ε with
  | zero =>
    refine ⟨C,Equiv.refl _,fun _ => 0,ActualColoredBlocks.nil,?_,?_,?_,hmass,hrC,?_⟩
    · intro r
      simpa [physicalError] using hε
    · simp
    · simp [blockPreviousError]
    · omega
  | succ K ih =>
    obtain ⟨E,α,A,hpath,hphys,hsqrt,hpred,hmassE,hrE,_hgoodE⟩ := ih (show 0 < ε/4 by positivity)
    obtain ⟨η,hη,hmassBudget⟩ := E.mass_transport_tolerance hmassE
    let e : ℝ := min η (ε/4)
    have he : 0 < e := lt_min hη (by positivity)
    obtain ⟨F,β,D,hblock,hphysB,hsqrtB,hpredB,hrF,hgoodF⟩ := actual_reflected_block E
      τR hτR hrE tags htags htrR hpath.estimator_continuous K hd hd1
      (sq_pos_of_pos hd) he hκ hmassE.le
    have hsmall r : physicalError (E.vector r) (F.vector r ∘ β) < η :=
      (hphysB r).trans_le (min_le_left _ _)
    have hmassF := hmassBudget F β D hblock hsmall
    refine ⟨F,α.trans β,fun z => A z+D z,hpath.snoc hblock,?_,?_,?_,hmassF,hrF,fun _ => hgoodF⟩
    · intro r
      have hmove : physicalError (E.vector r ∘ α) ((F.vector r ∘ β) ∘ α) < ε/4 := by
        rw [hpath.physicalError_eq]
        exact (hphysB r).trans_le (min_le_right _ _)
      have htriangle := physicalError_triangle (C.vector_continuous r)
        ((E.vector_continuous r).comp hpath.continuous)
        (((F.vector_continuous r).comp hblock.continuous).comp hpath.continuous)
      change physicalError (C.vector r) ((F.vector r ∘ β) ∘ α) < ε
      have hh := hphys r
      linarith
    · push_cast
      nlinarith [sq_nonneg delta]
    · rw [integral_blockPreviousError_eq (A := fun z => A z+D z) F.density_continuous tags
        (hpath.estimator_continuous.add hblock.estimator_continuous) (K+1)]
      simp only [Nat.cast_add,Nat.cast_one] at *
      have hinc := block_increment_budget hd hd1
      nlinarith

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

/-- δ and K are fixed before any block strengths or lengths, with the exact
source choice K=ceil(10/(ε²δ)). -/
lemma exists_prediction_budget {ε τ : ℝ} (hε : 0 < ε) (hτ : 0 < τ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      let K := ⌈10/(ε^2*δ)⌉₊
      0 < K ∧ 400*(K:ℝ)*δ^2 < τ ∧ 5/((K:ℝ)*δ) < ε^2 := by
  let δ := min (1/100) (min (ε^2*τ/16000) (τ/1600))/2
  have hd : 0 < δ := half_pos (lt_min (by norm_num)
    (lt_min (by positivity) (by positivity)))
  have hd1 : δ ≤ 1/100 := by
    have h := min_le_left (1/100:ℝ) (min (ε^2*τ/16000) (τ/1600))
    dsimp only [δ]
    linarith
  have hde : δ ≤ ε^2*τ/16000 := by
    have h := (min_le_right (1/100:ℝ) (min (ε^2*τ/16000) (τ/1600))).trans (min_le_left _ _)
    dsimp only [δ] at *
    linarith
  have hdt : δ ≤ τ/1600 := by
    have h := (min_le_right (1/100:ℝ) (min (ε^2*τ/16000) (τ/1600))).trans (min_le_right _ _)
    dsimp only [δ] at *
    linarith
  let K := ⌈10/(ε^2*δ)⌉₊
  have hden : 0 < ε^2*δ := mul_pos (sq_pos_of_pos hε) hd
  have hn0 : 0 < (K:ℝ) := (div_pos (by norm_num) hden).trans_le (Nat.le_ceil _)
  have hn : 0 < K := by exact_mod_cast hn0
  have hupper : (K:ℝ) < 10/(ε^2*δ)+1 := Nat.ceil_lt_add_one (by positivity)
  have heq : (10/(ε^2*δ)+1)*δ^2 = 10*δ/ε^2+δ^2 := by field_simp
  have hloss : 400*(K:ℝ)*δ^2 < τ := by
    have hm := mul_lt_mul_of_pos_right hupper (sq_pos_of_pos hd)
    rw [heq] at hm
    have h1 : 10*δ/ε^2 ≤ τ/1600 := (div_le_iff₀ (sq_pos_of_pos hε)).2 (by nlinarith)
    have h2 : δ^2 ≤ τ/1600 := by
      have : δ ≤ 1 := by linarith
      nlinarith
    nlinarith
  have hlower : 10 ≤ (K:ℝ)*(ε^2*δ) := (div_le_iff₀ hden).1 (Nat.le_ceil _)
  have hp : 5/((K:ℝ)*δ) < ε^2 := (div_lt_iff₀ (mul_pos hn0 hd)).2 (by nlinarith)
  exact ⟨δ,hd,hd1,hn,hloss,hp⟩

lemma averaged_prediction_identity {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r, Continuous (p r)) (b : Fin m → ℂ) {A : UnitAddCircle → ℂ}
    (hA : Continuous A) {K : ℕ} (hK : 0 < K) :
    (∑ r, ∫ z, p r z*‖A z/(K:ℂ)-b r‖^2 ∂phaseHaar) =
      (∫ z, blockPreviousError p b A K z ∂phaseHaar)/(K:ℝ)^2 := by
  classical
  have hKc : (K:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hK)
  have he (r : Fin m) (z : UnitAddCircle) :
      A z/(K:ℂ)-b r = (A z-(K:ℂ)*b r)/(K:ℂ) := by
    field_simp
  simp_rw [he,norm_div,Complex.norm_natCast,div_pow]
  simp_rw [← mul_div_assoc,integral_div]
  rw [← Finset.sum_div,integral_blockPreviousError_eq hp b hA]

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

/-- The source prediction estimate, for actual reflected packet passages.
The smooth-neighborhood requirement is not included here: it remains to be
threaded through the passage selection before exporting Proposition 4.1. -/
theorem actual_density_prediction {m : ℕ} (C : ColoredState (Fin m))
    (τR : Fin m → Fin m) (hτR : Involutive τR) (hrC : C.Reflection τR)
    (tags : Fin m → ℂ) (htags : ∀ r, ‖tags r‖ ≤ 1)
    (htrR : ∀ r, tags (τR r) = conj (tags r))
    {ε τ η κ : ℝ} (hε : 0 < ε) (hτ : 0 < τ) (hη : 0 < η) (hκ : 0 < κ)
    (hmass : (∫ z, blockTotal C.density z ∂phaseHaar) < 2) :
    ∃ E : ColoredState (Fin m), ∃ α : Equiv.Perm TripleTorus,
      ∃ Ψ : UnitAddCircle → ℂ, ∃ K : ℕ, ∃ A : UnitAddCircle → ℂ,
      0 < K ∧ ActualColoredBlocks C E K α A ∧ Ψ = (fun z => A z/(K:ℂ)) ∧
      (∀ r, physicalError (C.vector r) (E.vector r ∘ α) < η) ∧
      ((∫ z, Real.sqrt (blockTotal C.density z) ∂phaseHaar)-τ <
        ∫ z, Real.sqrt (blockTotal E.density z) ∂phaseHaar) ∧
      ((∑ r, ∫ z, E.density r z*‖Ψ z-tags r‖^2 ∂phaseHaar) < ε^2) ∧
      Continuous Ψ ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => Ψ (x:UnitAddCircle)) ∧
      (∀ z, Ψ (-z) = conj (Ψ z)) ∧
      (∫ z, blockTotal E.density z ∂phaseHaar) < 2 ∧ E.Reflection τR ∧
      ∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ E.packets.GoodArc δ := by
  obtain ⟨δ,hd,hd1,hK,hloss,hbudget⟩ := exists_prediction_budget hε hτ
  let K := ⌈10/(ε^2*δ)⌉₊
  change 0 < K at hK
  obtain ⟨E,α,A,hpath,hphys,hsqrt,hpred,hmassE,hrE,hgood⟩ :=
    actual_repeated_blocks C τR hτR hrC tags htags htrR hd hd1 hη hκ hmass K
  refine ⟨E,α,fun z => A z/(K:ℂ),K,A,hK,hpath,rfl,hphys,?_,?_,
    hpath.estimator_continuous.div_const _,hpath.estimator_smooth.div_const _,?_,
    hmassE,hrE,hgood hK⟩
  · change 400*(K:ℝ)*δ^2 < τ at hloss
    linarith
  · rw [averaged_prediction_identity E.density_continuous tags hpath.estimator_continuous hK]
    have hKr : 0 < (K:ℝ) := by exact_mod_cast hK
    have he : (K:ℝ)*(5/δ)/(K:ℝ)^2 = 5/((K:ℝ)*δ) := by field_simp
    exact (div_le_div_of_nonneg_right hpred (sq_nonneg _)).trans_lt (he ▸ hbudget)
  · intro z
    simp only [hpath.estimator_reflection]
    simp

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
namespace ColoredState
variable {m : ℕ} (C : ColoredState (Fin m))

/-- Literal packet spectral calculus, evaluated in the current coordinates. -/
def weightedVector (a : C.Index → UnitAddCircle → ℂ) (x : TripleTorus) : ℂ :=
  ∑ i, packet (C.packets.m i)
    (fun u => a i (C.packets.m i • (C.packets.periodic.lift u.1:UnitAddCircle))*C.packets.A i u) x

lemma weightedVector_continuous {a : C.Index → UnitAddCircle → ℂ}
    (ha : ∀ i, Continuous (a i)) : Continuous (C.weightedVector a) := by
  apply continuous_finsetSum
  intro i _
  apply continuous_packet
  exact ((ha i).comp (((AddCircle.continuous_mk' 1).comp
    (C.packets.speed_continuous.comp continuous_fst)).const_smul (C.packets.m i))).mul
    (C.packets.continuous_amplitude i)

lemma weighted_packet_spectral {a : UnitAddCircle → ℂ} (ha : Continuous a) (i : C.Index) :
    packetSpectralMeasure (fun x => (C.packets.periodic.lift x:UnitAddCircle)) (C.packets.m i)
      (fun u => a (C.packets.m i • (C.packets.periodic.lift u.1:UnitAddCircle))*C.packets.A i u) =
    phaseHaar.withDensity (fun z => ENNReal.ofReal (C.packets.density i z*‖a z‖^2)) := by
  have hz : Measurable (fun u : UnitAddCircle × UnitAddCircle =>
      C.packets.m i • (C.packets.periodic.lift u.1:UnitAddCircle)) :=
    ((((AddCircle.continuous_mk' 1).comp C.packets.speed_continuous).comp
      continuous_fst).const_smul (C.packets.m i)).measurable
  have hs := energy_map_multiplier hz (C.packets.continuous_amplitude i).measurable
    (C.packets.density_continuous i).measurable.ennreal_ofReal
    (C.packets.density_spectral C.spare i) ha.measurable
  have hh : (fun z => ENNReal.ofReal (C.packets.density i z*‖a z‖^2)) =
      (fun z => ENNReal.ofReal (C.packets.density i z))*energyWeight a := by
    funext z
    exact ENNReal.ofReal_mul (C.packets.density_nonneg i z)
  rw [hh]
  exact hs

lemma weightedVector_energy {a : C.Index → UnitAddCircle → ℂ}
    (ha : ∀ i, Continuous (a i)) :
    (∫ x, ‖C.weightedVector a x‖^2 ∂tripleVolume) =
      ∑ i, ∫ z, C.packets.density i z*‖a i z‖^2 ∂phaseHaar := by
  let B (i : C.Index) (u : UnitAddCircle × UnitAddCircle) : ℂ :=
    a i (C.packets.m i • (C.packets.periodic.lift u.1:UnitAddCircle))*C.packets.A i u
  have hB (i : C.Index) : Continuous (B i) :=
    ((ha i).comp (((AddCircle.continuous_mk' 1).comp
      (C.packets.speed_continuous.comp continuous_fst)).const_smul (C.packets.m i))).mul
      (C.packets.continuous_amplitude i)
  have hφ : Continuous (fun x => (C.packets.periodic.lift x:UnitAddCircle)) :=
    (AddCircle.continuous_mk' 1).comp C.packets.speed_continuous
  have h := disjoint_packet_list_correlation C.packets.m B hB hφ
    (fun i j hij hm => (hij (C.injective hm)).elim) 0
  have he (x : TripleTorus) :
      conj (∑ i, packet (C.packets.m i) (B i) x)*
      (∑ i, packet (C.packets.m i) (B i)
        (twistIter (fun u => (C.packets.periodic.lift u:UnitAddCircle)) 0 x)) =
      ((‖C.weightedVector a x‖^2:ℝ):ℂ) := by
    simp only [twistIter,zero_zsmul,add_zero]
    change conj (C.weightedVector a x)*C.weightedVector a x = _
    rw [mul_comm,Complex.mul_conj,Complex.sq_norm]
  simp_rw [he] at h
  change _ = ∑ i, ∫ z, fourier 0 z ∂packetSpectralMeasure _ _ _ at h
  dsimp only [B] at h
  simp_rw [C.weighted_packet_spectral (ha _)] at h
  have hm (i : C.Index) : (∫ z, fourier 0 z ∂phaseHaar.withDensity
      (fun z => ENNReal.ofReal (C.packets.density i z*‖a i z‖^2))) =
      ((∫ z, C.packets.density i z*‖a i z‖^2 ∂phaseHaar:ℝ):ℂ) := by
    erw [moment_withDensity_real
      (((C.packets.density_continuous i).mul ((ha i).norm.pow 2)).measurable)
      (fun z => mul_nonneg (C.packets.density_nonneg i z) (sq_nonneg _)) (fourier 0)]
    simp only [fourier_zero,mul_one,integral_complex_ofReal]
    rfl
  simp_rw [hm] at h
  rw [integral_complex_ofReal,← Complex.ofReal_sum] at h
  exact Complex.ofReal_injective h

lemma weightedVector_sub (a b : C.Index → UnitAddCircle → ℂ) (x : TripleTorus) :
    C.weightedVector (fun i z => a i z-b i z) x =
      C.weightedVector a x-C.weightedVector b x := by
  simp only [weightedVector,packet,sub_mul,Finset.sum_sub_distrib]

lemma weightedVector_tags (b : Fin m → ℂ) (x : TripleTorus) :
    C.weightedVector (fun i _ => b (C.color i)) x = ∑ r, b r*C.vector r x := by
  classical
  simp only [weightedVector,vector,colorVector,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_ite,mul_zero]
  simp [packet,mul_assoc]

lemma weighted_density_colors (b : Fin m → ℂ) {Ψ : UnitAddCircle → ℂ}
    (hΨ : Continuous Ψ) :
    (∑ i, ∫ z, C.packets.density i z*‖Ψ z-b (C.color i)‖^2 ∂phaseHaar) =
      ∑ r, ∫ z, C.density r z*‖Ψ z-b r‖^2 ∂phaseHaar := by
  classical
  have hint (i : C.Index) (r : Fin m) : Integrable
      (fun z => (if C.color i = r then C.packets.density i z else 0)*‖Ψ z-b r‖^2) phaseHaar := by
    apply continuous_circle_integrable
    split_ifs
    · exact (C.packets.density_continuous i).mul ((hΨ.sub continuous_const).norm.pow 2)
    · fun_prop
  simp only [density,colorDensity,Finset.sum_mul]
  simp_rw [integral_finsetSum _ (fun i _ => hint i _)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have he (r : Fin m) : (∫ z, (if C.color i = r then C.packets.density i z else 0)*
      ‖Ψ z-b r‖^2 ∂phaseHaar) =
      if C.color i = r then (∫ z, C.packets.density i z*‖Ψ z-b r‖^2 ∂phaseHaar) else 0 := by
    split_ifs <;> simp_all
  simp_rw [he]
  simp

/-- The density prediction error is exactly the squared physical L² error
for the literal packet multiplier; no cyclic-space calculus is assumed. -/
lemma physical_prediction_energy (b : Fin m → ℂ) {Ψ : UnitAddCircle → ℂ}
    (hΨ : Continuous Ψ) :
    (∫ x, ‖C.weightedVector (fun _ => Ψ) x-∑ r, b r*C.vector r x‖^2 ∂tripleVolume) =
      ∑ r, ∫ z, C.density r z*‖Ψ z-b r‖^2 ∂phaseHaar := by
  simp_rw [← C.weightedVector_tags,← C.weightedVector_sub]
  have hh (i : C.Index) : Continuous (fun z => Ψ z-b (C.color i)) :=
    hΨ.sub continuous_const
  rw [C.weightedVector_energy hh]
  exact C.weighted_density_colors b hΨ

end ColoredState
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
namespace ColoredState
variable {m : ℕ} (C : ColoredState (Fin m))

/-- A finite Laurent polynomial in the actual twist Koopman operator. -/
def laurent (c : ℤ →₀ ℂ) (x : TripleTorus) : ℂ :=
  ∑ k ∈ c.support, c k*C.totalVector
    (twistIter (fun u => (C.packets.periodic.lift u:UnitAddCircle)) k x)

lemma laurent_eq_multiplier (c : ℤ →₀ ℂ) (x : TripleTorus) :
    C.laurent c x = C.weightedVector (fun _ z => ∑ k ∈ c.support, c k*fourier k z) x := by
  simp only [laurent,C.totalVector_eq,Finset.mul_sum]
  simp only [packet_twistIter]
  simp only [weightedVector,packet]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma laurent_continuous (c : ℤ →₀ ℂ) : Continuous (C.laurent c) := by
  have hh : C.laurent c = C.weightedVector (fun _ z => ∑ k ∈ c.support, c k*fourier k z) :=
    funext (C.laurent_eq_multiplier c)
  rw [hh]
  exact C.weightedVector_continuous (fun _ => continuous_finsetSum _
    (fun k _ => continuous_const.mul (fourier k).continuous))

lemma multiplier_error_bound {Ψ Φ : UnitAddCircle → ℂ} (hΨ : Continuous Ψ) (hΦ : Continuous Φ)
    {δ : ℝ} (hbound : ∀ z, ‖Ψ z-Φ z‖ ≤ δ) :
    physicalError (C.weightedVector (fun _ => Ψ)) (C.weightedVector (fun _ => Φ)) ≤
      δ^2*(∫ z, blockTotal C.density z ∂phaseHaar) := by
  unfold physicalError
  simp_rw [← C.weightedVector_sub]
  have hh (i : C.Index) : Continuous (fun z => Ψ z-Φ z) := hΨ.sub hΦ
  rw [C.weightedVector_energy hh]
  have he : (∑ i, ∫ z, C.packets.density i z*‖Ψ z-Φ z‖^2 ∂phaseHaar) =
      ∫ z, (blockTotal C.density z)*‖Ψ z-Φ z‖^2 ∂phaseHaar := by
    simp_rw [C.totalDensity_eq,Finset.sum_mul]
    exact (integral_finsetSum _ (fun i _ => continuous_circle_integrable
      ((C.packets.density_continuous i).mul ((hΨ.sub hΦ).norm.pow 2)))).symm
  rw [he]
  calc
    _ ≤ ∫ z, (blockTotal C.density z)*δ^2 ∂phaseHaar := by
      apply integral_mono
      · exact continuous_circle_integrable ((continuous_finsetSum _ (fun r _ => C.density_continuous r)).mul
          ((hΨ.sub hΦ).norm.pow 2))
      · exact continuous_circle_integrable ((continuous_finsetSum _ (fun r _ => C.density_continuous r)).mul continuous_const)
      · intro z
        apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun r _ => C.density_nonneg r z))
        exact pow_le_pow_left₀ (norm_nonneg _) (hbound z) 2
    _ = _ := by rw [integral_mul_const,mul_comm]

/-- Continuous spectral multiplication lies in the physical cyclic space,
proved by actual finite Laurent approximants, with any squared L² tolerance. -/
lemma exists_laurent_approx {Ψ : UnitAddCircle → ℂ} (hΨ : Continuous Ψ)
    {ε : ℝ} (he : 0 < ε) :
    ∃ c : ℤ →₀ ℂ, physicalError (C.weightedVector (fun _ => Ψ)) (C.laurent c) < ε := by
  let M := ∫ z, blockTotal C.density z ∂phaseHaar
  have hM : 0 ≤ M := integral_nonneg (fun z => Finset.sum_nonneg (fun r _ => C.density_nonneg r z))
  let δ := min 1 (ε/(M+1))/2
  have hd : 0 < δ := half_pos (lt_min zero_lt_one (div_pos he (by positivity)))
  have hd1 : δ ≤ 1 := by dsimp only [δ]; linarith [min_le_left (1:ℝ) (ε/(M+1))]
  have hdε : δ*(M+1) < ε := by
    have hi := min_le_right (1:ℝ) (ε/(M+1))
    have heq : (ε/(M+1))*(M+1) = ε := div_mul_cancel₀ _ (by positivity)
    have hq : 0 < ε/(M+1) := div_pos he (by positivity)
    have hh : δ < ε/(M+1) := by dsimp only [δ]; linarith
    have hb := mul_lt_mul_of_pos_right hh (show 0 < M+1 by positivity)
    linarith
  have hsmall : δ^2*M < ε := by
    have hg : δ^2 ≤ δ := by nlinarith
    have hh := mul_le_mul_of_nonneg_right hg hM
    nlinarith
  obtain ⟨c,hc⟩ := exists_uniform_laurent hΨ hd
  refine ⟨c,?_⟩
  have hΦ : Continuous (fun z : UnitAddCircle => ∑ k ∈ c.support, c k*fourier k z) :=
    continuous_finsetSum _ (fun k _ => continuous_const.mul (fourier k).continuous)
  have hb := C.multiplier_error_bound hΨ hΦ (fun z => (hc z).le)
  have hv : C.laurent c = C.weightedVector (fun _ z => ∑ k ∈ c.support, c k*fourier k z) :=
    funext (C.laurent_eq_multiplier c)
  rw [← hv] at hb
  exact hb.trans_lt hsmall

end ColoredState
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma physicalError_symm (f g : TripleTorus → ℂ) : physicalError f g = physicalError g f := by
  unfold physicalError
  simp only [norm_sub_rev]

lemma physicalError_const_mul {f g : TripleTorus → ℂ} (b : ℂ) :
    physicalError (fun x => b*f x) (fun x => b*g x) = ‖b‖^2*physicalError f g := by
  unfold physicalError
  simp_rw [← mul_sub,norm_mul,mul_pow]
  rw [integral_const_mul]

lemma physicalError_tagged_sum {m : ℕ} {f g : Fin m → TripleTorus → ℂ}
    (hf : ∀ r, Continuous (f r)) (hg : ∀ r, Continuous (g r))
    (b : Fin m → ℂ) (hb : ∀ r, ‖b r‖ ≤ 1) {η : ℝ}
    (he : ∀ r, physicalError (f r) (g r) ≤ η) :
    physicalError (fun x => ∑ r, b r*f r x) (fun x => ∑ r, b r*g r x) ≤ (m:ℝ)^2*η := by
  have ht := physicalError_sum (fun r => continuous_const.mul (hf r))
    (fun r => continuous_const.mul (hg r)) (f := fun r x => b r*f r x) (g := fun r x => b r*g r x)
  simp_rw [physicalError_const_mul] at ht
  have hi r : ‖b r‖^2*physicalError (f r) (g r) ≤ η := by
    have hsq := pow_le_pow_left₀ (norm_nonneg (b r)) (hb r) 2
    calc
      _ ≤ 1*physicalError (f r) (g r) := mul_le_mul_of_nonneg_right (by simpa using hsq) (physicalError_nonneg _ _)
      _ ≤ η := by simpa using he r
  have hs := Finset.sum_le_sum (fun r (_ : r ∈ (Finset.univ : Finset (Fin m))) => hi r)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs ht
  have hn : 0 ≤ (m:ℝ) := Nat.cast_nonneg _
  have hm := mul_le_mul_of_nonneg_left hs hn
  nlinarith

/-- Actual finite Laurent approximation to the OLD tagged packet sum after
reflected signal blocks. Neither a cyclic-space oracle nor a formal spectral
operator is used: the witness is a literal finite sum of twist iterates. -/
theorem actual_cyclic_prediction {m : ℕ} (C : ColoredState (Fin m))
    (τR : Fin m → Fin m) (hτR : Involutive τR) (hrC : C.Reflection τR)
    (tags : Fin m → ℂ) (htags : ∀ r, ‖tags r‖ ≤ 1)
    (htrR : ∀ r, tags (τR r) = conj (tags r))
    {ε τ η κ : ℝ} (hε : 0 < ε) (hτ : 0 < τ) (hη : 0 < η) (hκ : 0 < κ)
    (hmass : (∫ z, blockTotal C.density z ∂phaseHaar) < 2) :
    ∃ E : ColoredState (Fin m), ∃ α : Equiv.Perm TripleTorus,
      ∃ c : ℤ →₀ ℂ, ∃ K : ℕ, ∃ A : UnitAddCircle → ℂ,
      0 < K ∧ ActualColoredBlocks C E K α A ∧
      (∀ r, physicalError (C.vector r) (E.vector r ∘ α) < η) ∧
      ((∫ z, Real.sqrt (blockTotal C.density z) ∂phaseHaar)-τ <
        ∫ z, Real.sqrt (blockTotal E.density z) ∂phaseHaar) ∧
      physicalError (fun x => ∑ r, tags r*C.vector r x) (E.laurent c ∘ α) < ε^2 ∧
      (∫ z, blockTotal E.density z ∂phaseHaar) < 2 ∧ E.Reflection τR ∧
      ∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ E.packets.GoodArc δ := by
  let e := min η (ε^2/(16*((m:ℝ)+1)^2))
  have he : 0 < e := lt_min hη (div_pos (sq_pos_of_pos hε) (by positivity))
  obtain ⟨E,α,Ψ,K,A,hK,hpath,hΨdef,hphys,hsqrt,hpred,hΨ,_,_,hmassE,hrE,hgood⟩ :=
    actual_density_prediction C τR hτR hrC tags htags htrR (show 0 < ε/8 by positivity)
      hτ he hκ hmass
  obtain ⟨c,hc⟩ := E.exists_laurent_approx hΨ (show 0 < ε^2/64 by positivity)
  refine ⟨E,α,c,K,A,hK,hpath,fun r => (hphys r).trans_le (min_le_left _ _),hsqrt,?_,hmassE,hrE,hgood⟩
  let G : TripleTorus → ℂ := fun x => ∑ r, tags r*E.vector r x
  let F : TripleTorus → ℂ := fun x => ∑ r, tags r*C.vector r x
  let W := E.weightedVector (fun _ => Ψ)
  have hG : Continuous G := continuous_finsetSum _ (fun r _ => continuous_const.mul (E.vector_continuous r))
  have hF : Continuous F := continuous_finsetSum _ (fun r _ => continuous_const.mul (C.vector_continuous r))
  have hW : Continuous W := E.weightedVector_continuous (fun _ => hΨ)
  have hp : physicalError G W < (ε/8)^2 := by
    rw [physicalError_symm]
    exact (E.physical_prediction_energy tags hΨ).trans_lt hpred
  have ht := physicalError_triangle hG hW (E.laurent_continuous c)
  have heL : physicalError G (E.laurent c) < ε^2/16 := by linarith
  have htag : physicalError F (G ∘ α) ≤ (m:ℝ)^2*e :=
    physicalError_tagged_sum C.vector_continuous
      (fun r => (E.vector_continuous r).comp hpath.continuous) tags htags
      (fun r => (hphys r).le)
  have hsmall : (m:ℝ)^2*e < ε^2/16 := by
    have he' : e ≤ ε^2/(16*((m:ℝ)+1)^2) := min_le_right _ _
    have hm : 0 ≤ (m:ℝ) := Nat.cast_nonneg _
    have hden : 0 < 16*((m:ℝ)+1)^2 := by positivity
    have hmul : e*(16*((m:ℝ)+1)^2) ≤ ε^2 := (le_div_iff₀ hden).1 he'
    nlinarith [sq_nonneg (m:ℝ)]
  have hlast := physicalError_triangle hF (hG.comp hpath.continuous)
    ((E.laurent_continuous c).comp hpath.continuous)
  rw [hpath.physicalError_eq] at hlast
  change physicalError F (E.laurent c ∘ α) < ε^2
  linarith [sq_pos_of_pos hε]

end ThreeTorus
end
end

section

noncomputable section
open Set Function MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma physicalDist_const_mul {f g : TripleTorus → ℂ} (b : ℂ) :
    physicalDist (fun x => b*f x) (fun x => b*g x) = ‖b‖*physicalDist f g := by
  rw [physicalDist,physicalError_const_mul,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (norm_nonneg _)]
  rfl

lemma finite_weighted_dist_le {ι : Type*} [Fintype ι] {f g : ι → TripleTorus → ℂ}
    (hf : ∀ i, Continuous (f i)) (hg : ∀ i, Continuous (g i))
    (b : ι → ℂ) {r : ℝ} (hd : ∀ i, physicalDist (f i) (g i) ≤ r) :
    physicalDist (fun x => ∑ i, b i*f i x) (fun x => ∑ i, b i*g i x) ≤ (∑ i, ‖b i‖)*r := by
  calc
    _ ≤ ∑ i, physicalDist (fun x => b i*f i x) (fun x => b i*g i x) :=
      physicalDist_finsum (fun i => (continuous_const.mul (hf i)).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (fun i => (continuous_const.mul (hg i)).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    _ ≤ ∑ i, ‖b i‖*r := by
      simp_rw [physicalDist_const_mul]
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hd i) (norm_nonneg _))
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- The TWO separating passages simultaneously approximate the total vector,
its arbitrarily tagged test, and total density. Tags are fixed BEFORE choice. -/
theorem exists_colored_separation_small {n : ℕ} (F : PassagePackets (Fin n))
    (hd : ∀ i j, i ≠ j → F.m i = F.m j → Disjoint (F.cylinderCore i) (F.cylinderCore j))
    (τ : Fin n → Fin n) (hτ : Involutive τ) (hr : F.Reflection τ)
    (b : Fin n → ℂ) (Q : PhysicalJetData) (frame : PhysicalFrame)
    {ε κ ζ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hζ : 0 < ζ) :
    ∃ C : ColoredState (Fin n), ∃ α : Equiv.Perm TripleTorus, ∃ frame' : PhysicalFrame,
      Continuous α ∧ MeasurePreserving α tripleVolume tripleVolume ∧
      frame'.chart=frame.chart.trans α ∧ C.Reflection τ ∧
      (∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ C.packets.GoodArc δ) ∧
      Q.Close ζ frame F.V frame' C.packets.V ∧
      physicalDist (finitePacketVector F.m F.A) (C.totalVector ∘ α) < ε ∧
      physicalDist (fun x => ∑ i, b i*packet (F.m i) (F.A i) x)
        ((fun x => ∑ i, b i*C.vector i x) ∘ α) < ε ∧
      (∫ z, |blockTotal C.density z-(∑ i, F.marginalDensity i z)| ∂phaseHaar) < ε := by
  classical
  let B : ℝ := n+∑ i, ‖b i‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let r := min (ε/(B+1)) 1
  have hrp : 0 < r := lt_min (div_pos hε (by positivity)) zero_lt_one
  have hr1 : r ≤ 1 := min_le_right _ _
  have hbr : (B+1)*r ≤ ε := by
    have hh := (le_div_iff₀ (by positivity : 0 < B+1)).1 (min_le_left (ε/(B+1)) 1)
    dsimp [r]; nlinarith
  have hnr : (n:ℝ)*r < ε := by
    have hn : (n:ℝ) ≤ B := by dsimp [B]; exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => norm_nonneg _))
    nlinarith
  have htr : (∑ i, ‖b i‖)*r < ε := by
    have hn : (∑ i, ‖b i‖) ≤ B := by dsimp [B]; exact le_add_of_nonneg_left (Nat.cast_nonneg _)
    nlinarith
  obtain ⟨C,α,frame',hαc,hαm,hfr,hCr,hgood,hjet,herr⟩ :=
    exists_colored_separation F hd τ hτ hr Q frame (sq_pos_of_pos hrp) hκ hζ
  have hdist (i : Fin n) : physicalDist (packet (F.m i) (F.A i)) (C.vector i ∘ α) ≤ r :=
    ((physicalDist_lt_iff _ _ hrp).2 (herr i).1).le
  refine ⟨C,α,frame',hαc,hαm,hfr,hCr,hgood,hjet,?_,?_,?_⟩
  · have hh := finite_weighted_dist_le (fun i => continuous_packet (F.continuous_amplitude i))
      (fun i => (C.vector_continuous i).comp hαc) (fun _ => (1:ℂ)) hdist
    simp only [one_mul,norm_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hh
    exact hh.trans_lt hnr
  · exact (finite_weighted_dist_le (fun i => continuous_packet (F.continuous_amplitude i))
      (fun i => (C.vector_continuous i).comp hαc) b hdist).trans_lt htr
  · have hh := integral_abs_sum_sub_le_of_integrable
      (fun i => (C.density_continuous i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (fun i => F.marginalDensity_integrable i)
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => (herr i).2.le)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
    refine (hh.trans hsum).trans_lt ?_
    have hn := Nat.cast_nonneg (α := ℝ) n
    nlinarith
end ThreeTorus
end
end

section

noncomputable section
open Set Function MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

/-- Full source05 preparation through BOTH support-separating passages. The
same arbitrary tags, reality, physical errors and total density are retained. -/
theorem exists_prediction_ready (F : MeasurablePackets)
    {τ : F.Index → F.Index} (hr : F.Reflection τ)
    {δ l u : ℝ} (hδ : 0 ≤ δ) (hd : δ < 1/2) (hdl : δ < l) (hud : u < 1-δ)
    (hsupp : F.Supported l u)
    (V : ℝ → ℝ) (hp : Periodic V 1) (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hv : ∀ x ∈ Ioo δ (1-δ), 0 < deriv V x)
    (hflat : F.spectrum (fun z => (hp.lift z:UnitAddCircle))=phaseHaar)
    {h : TripleTorus → ℂ} (hh : Continuous h) (hrh : ∀ x, conj (h x)=h x)
    (hch : ∫ x, h x ∂tripleVolume=0) (hbh : ∀ x, ‖h x‖ ≤ 1)
    (Q : PhysicalJetData) (frame : PhysicalFrame)
    {ε κ ζ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hζ : 0 < ζ) :
    ∃ n : ℕ, ∃ C : ColoredState (Fin n), ∃ ρ : Fin n → Fin n,
      ∃ b : Fin n → ℂ, ∃ α : Equiv.Perm TripleTorus, ∃ frame' : PhysicalFrame,
      Continuous α ∧ MeasurePreserving α tripleVolume tripleVolume ∧
      frame'.chart=frame.chart.trans α ∧ Involutive ρ ∧ C.Reflection ρ ∧
      (∀ i, b (ρ i)=conj (b i)) ∧
      (∃ δ' : ℝ, 0 < δ' ∧ δ' < 1/8 ∧ δ' < κ ∧ C.packets.GoodArc δ') ∧
      Q.Close ζ frame V frame' C.packets.V ∧
      physicalDist F.vector (C.totalVector ∘ α) < ε ∧
      physicalDist h ((fun x => ∑ i, b i*C.vector i x) ∘ α) < Real.sqrt (2*δ)+ε ∧
      (∫ z, |blockTotal C.density z-1| ∂phaseHaar) < ε := by
  classical
  let e := min (ε/32) (1/32)
  have he : 0 < e := lt_min (by positivity) (by norm_num)
  have he1 : e < 1/4 := (min_le_right _ _).trans_lt (by norm_num)
  have heε : 32*e ≤ ε := by have := min_le_left (ε/32) (1/32); dsimp [e]; linarith
  obtain ⟨G,H,α,P,hαc,hαm,hP,hHV,hGi,⟨d,hd0,hd8,hdκ,hGg,hHg⟩,hjet,hFG,hHH,hpG⟩ :=
    exists_prepared_pair F hr hδ hd hdl hud hsupp V hp hs hv hflat hh hrh hch hbh Q frame he hκ (half_pos hζ)
  obtain ⟨n,R,ρ,b,hRV,hRg,hρ,hRr,hb,hdR,hGR,hHR⟩ :=
    exists_ratio_packets_for_pair G.data H.data hd0.le hGg hHg hHV G.neg H.neg
      G.invol H.invol G.reflected H.reflected he
  let R' : RealPacketFamily := ⟨Fin n,inferInstance,R,ρ,hρ,hRr⟩
  change physicalDist G.vector R'.vector < e at hGR
  change physicalDist H.vector (fun x => ∑ i, b i*packet (R.m i) (R.A i) x) < e at hHR
  have hφ : Measurable (fun z => (hp.lift z:UnitAddCircle)) :=
    AddCircle.measurable_mk'.comp (continuous_of_continuous_lift (by simpa only [Periodic.lift_coe] using hs.continuous)).measurable
  have hf1 := F.flat_norm hφ hflat
  have hnG : physicalDist G.vector 0 < 1+e := by
    have ht := physicalDist_triangle (continuous_triple_memLp (G.continuous_vector.comp hαc)) F.vector_memLp MemLp.zero
    rw [physicalDist_symm (G.vector ∘ α) F.vector,hf1] at ht
    have hz : (0 : TripleTorus → ℂ) ∘ α = 0 := rfl
    rw [← hz,physicalDist_continuous_comp α hαc hαm] at ht
    linarith
  have hnR : physicalDist R'.vector 0 < 1+2*e := by
    have ht := physicalDist_triangle R'.vector_memLp G.vector_memLp MemLp.zero
    rw [physicalDist_symm R'.vector G.vector] at ht
    change physicalDist G.vector R'.vector < e at hGR
    linarith
  have hpR : (∫ z, |R'.density z-G.density z| ∂phaseHaar) < 4*e := by
    have hh := G.data.marginalDensity_distance R hRV
      (by intro x i j hij hm; exact (hij (hGi hm)).elim)
      (R.amplitude_disjoint_of_cylinderCore hdR)
    change (∫ z, |G.density z-R'.density z| ∂phaseHaar) ≤
      (physicalDist G.vector 0+physicalDist R'.vector 0)*physicalDist G.vector R'.vector at hh
    have hnorm : physicalDist G.vector 0+physicalDist R'.vector 0 < 4 := by linarith
    have hmp := mul_le_mul_of_nonneg_left hGR.le (add_nonneg (physicalDist_nonneg G.vector 0) (physicalDist_nonneg R'.vector 0))
    simp_rw [abs_sub_comm (R'.density _) (G.density _)]
    exact (hh.trans hmp).trans_lt (mul_lt_mul_of_pos_right hnorm he)
  obtain ⟨C,β,P',hβc,hβm,hP',hCr,hgood,hjet',hRC,hRb,hpC⟩ :=
    exists_colored_separation_small R hdR ρ hρ hRr b Q P he hκ (half_pos hζ)
  have hβac : Continuous (α.trans β) := hβc.comp hαc
  have hβam : MeasurePreserving (α.trans β) tripleVolume tripleVolume := hβm.comp hαm
  have hRC' : physicalDist (R'.vector ∘ α) (C.totalVector ∘ (α.trans β)) < e := by
    change physicalDist (R'.vector ∘ α) ((C.totalVector ∘ β) ∘ α) < e
    rw [physicalDist_continuous_comp α hαc hαm]
    exact hRC
  have hGR' : physicalDist (G.vector ∘ α) (R'.vector ∘ α) < e := by
    rw [physicalDist_continuous_comp α hαc hαm]
    exact hGR
  have hHC' : physicalDist (H.vector ∘ α)
      ((fun x => ∑ i, b i*C.vector i x) ∘ (α.trans β)) < 2*e := by
    have htag : Continuous (fun x => ∑ i, b i*packet (R.m i) (R.A i) x) :=
      continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_packet (R.continuous_amplitude i)))
    have hctag : Continuous (fun x => ∑ i, b i*C.vector i x) :=
      continuous_finsetSum _ (fun i _ => continuous_const.mul (C.vector_continuous i))
    change physicalDist (H.vector ∘ α) (((fun x => ∑ i, b i*C.vector i x) ∘ β) ∘ α) < 2*e
    rw [physicalDist_continuous_comp α hαc hαm]
    exact (physicalDist_triangle H.vector_memLp (continuous_triple_memLp htag)
      (continuous_triple_memLp (hctag.comp hβc))).trans_lt (by linarith)
  refine ⟨n,C,ρ,b,α.trans β,P',hβac,hβam,?_,hρ,hCr,hb,hgood,?_,?_,?_,?_⟩
  · rw [hP',hP]; rfl
  · rw [hRV] at hjet'
    exact (hjet.trans hjet').mono (by linarith)
  · have ht := physicalDist_triangle (continuous_triple_memLp (G.continuous_vector.comp hαc))
      (continuous_triple_memLp (R'.continuous_vector.comp hαc))
      (continuous_triple_memLp (C.totalVector_continuous.comp hβac))
    have ht' := physicalDist_triangle F.vector_memLp (continuous_triple_memLp (G.continuous_vector.comp hαc))
      (continuous_triple_memLp (C.totalVector_continuous.comp hβac))
    linarith
  · have hctag : Continuous (fun x => ∑ i, b i*C.vector i x) :=
      continuous_finsetSum _ (fun i _ => continuous_const.mul (C.vector_continuous i))
    have ht := physicalDist_triangle (continuous_triple_memLp hh) (continuous_triple_memLp (H.continuous_vector.comp hαc))
      (continuous_triple_memLp (hctag.comp hβac))
    linarith
  · have hpCi : Integrable (blockTotal C.density) phaseHaar :=
      integrable_finsetSum _ (fun i _ => (C.density_continuous i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    have ht := densityDist_triangle hpCi R'.density_integrable G.density_integrable
    have ht' := densityDist_triangle hpCi G.density_integrable (integrable_const (1:ℝ))
    change (∫ z, |blockTotal C.density z-R'.density z| ∂phaseHaar) < e at hpC
    linarith
end ThreeTorus
end
end

end OAI
