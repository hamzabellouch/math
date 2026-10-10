import OAI.Dynamics.ThreeTorus.TensorPackets

namespace OAI

/-! Laurent prediction, flat packet filling, color energies, measurable packets, reflected smoothing, and prepared pairs. -/

section

noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal NNReal Topology BigOperators ComplexConjugate
namespace ThreeTorus
section FinitePacket
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma memLp_multiplyPackets {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (m : ι → ℤ) {a : UnitAddCircle → ℂ} (ha : Continuous a)
    {A : ι → UnitAddCircle × UnitAddCircle → ℂ} (hAm : ∀ i, Measurable (A i))
    (hA : ∀ i, MemLp (A i) 2 slowVolume) (i : ι) :
    MemLp (multiplyPackets φ m a A i) 2 slowVolume := by
  obtain ⟨C,hC⟩ := (isCompact_range ha).isBounded.exists_norm_le
  apply (hA i).of_le_mul (measurable_multiplyPackets hφ m ha.measurable hAm i).aestronglyMeasurable
  filter_upwards [] with ua
  exact (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_right (hC _ (mem_range_self _)) (norm_nonneg _))

lemma multiplyPackets_energy_flat {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    {m : ι → ℤ} (hm : Injective m) {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hA : ∀ i, MemLp (A i) 2 slowVolume)
    (hflat : finitePacketSpectralMeasure φ m A = phaseHaar)
    {a : UnitAddCircle → ℂ} (ha : Continuous a) :
    (∫ x, ‖finitePacketVector m (multiplyPackets φ m a A) x‖^2 ∂tripleVolume) =
      ∫ z, ‖a z‖^2 ∂phaseHaar := by
  have hpush : finitePacketSpectralMeasure φ m A = phaseHaar.withDensity (fun _ => ENNReal.ofReal (1:ℝ)) := by
    simpa only [ENNReal.ofReal_one,withDensity_const,one_smul] using hflat
  have he := multiplyPackets_spectrum hφ m measurable_const (fun _ => zero_le_one) hAm hpush ha.measurable
  simp only [one_mul] at he
  exact finitePacket_energy_density hφ hm (measurable_multiplyPackets hφ m ha.measurable hAm)
    (memLp_multiplyPackets hφ m ha hAm hA) (ha.measurable.norm.pow_const 2) (fun _ => sq_nonneg _) he

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma multiplyPackets_sub (φ : UnitAddCircle → UnitAddCircle) (m : ι → ℤ)
    (a b : UnitAddCircle → ℂ) (A : ι → UnitAddCircle × UnitAddCircle → ℂ) :
    multiplyPackets φ m (fun z => a z-b z) A =
      fun i ua => multiplyPackets φ m a A i ua - multiplyPackets φ m b A i ua := by
  funext i ua
  exact sub_mul _ _ _

lemma multiplyPackets_distance_flat {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    {m : ι → ℤ} (hm : Injective m) {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hA : ∀ i, MemLp (A i) 2 slowVolume)
    (hflat : finitePacketSpectralMeasure φ m A = phaseHaar)
    {a b : UnitAddCircle → ℂ} (ha : Continuous a) (hb : Continuous b) :
    (∫ x, ‖finitePacketVector m (multiplyPackets φ m a A) x -
      finitePacketVector m (multiplyPackets φ m b A) x‖^2 ∂tripleVolume) =
      ∫ z, ‖a z-b z‖^2 ∂phaseHaar := by
  simp_rw [← congrFun (finitePacketVector_sub m (multiplyPackets φ m a A) (multiplyPackets φ m b A))]
  rw [← multiplyPackets_sub]
  exact multiplyPackets_energy_flat hφ hm hAm hA hflat (ha.sub hb)

/-- A literal finite Laurent polynomial in the Koopman orbit of a measurable packet vector. -/
def finitePacketLaurent (φ : UnitAddCircle → UnitAddCircle) (m : ι → ℤ)
    (A : ι → UnitAddCircle × UnitAddCircle → ℂ) (c : ℤ →₀ ℂ) (x : TripleTorus) : ℂ :=
  ∑ k ∈ c.support, c k*finitePacketVector m A (twistIter φ k x)

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma finitePacketLaurent_eq_multiplier (φ : UnitAddCircle → UnitAddCircle) (m : ι → ℤ)
    (A : ι → UnitAddCircle × UnitAddCircle → ℂ) (c : ℤ →₀ ℂ) (x : TripleTorus) :
    finitePacketLaurent φ m A c x =
      finitePacketVector m (multiplyPackets φ m (fun z => ∑ k ∈ c.support, c k*fourier k z) A) x := by
  simp only [finitePacketLaurent,finitePacketVector,Finset.mul_sum,packet_twistIter]
  simp only [multiplyPackets,packet]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma exists_finitePacketLaurent_approx {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    {m : ι → ℤ} (hm : Injective m) {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hA : ∀ i, MemLp (A i) 2 slowVolume)
    (hflat : finitePacketSpectralMeasure φ m A = phaseHaar)
    {a : UnitAddCircle → ℂ} (ha : Continuous a) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℤ →₀ ℂ, (∫ x, ‖finitePacketVector m (multiplyPackets φ m a A) x -
      finitePacketLaurent φ m A c x‖^2 ∂tripleVolume) < ε^2 := by
  obtain ⟨c,hc⟩ := exists_uniform_laurent ha (show 0 < ε/2 by positivity)
  refine ⟨c,?_⟩
  simp_rw [finitePacketLaurent_eq_multiplier]
  have hpoly : Continuous (fun z : UnitAddCircle => ∑ k ∈ c.support, c k*fourier k z) :=
    continuous_finsetSum _ (fun k _ => continuous_const.mul (fourier k).continuous)
  rw [multiplyPackets_distance_flat hφ hm hAm hA hflat ha hpoly]
  have hi : (∫ z, ‖a z-∑ k ∈ c.support, c k*fourier k z‖^2 ∂phaseHaar) ≤ (ε/2)^2 := by
    calc
      _ ≤ ∫ _z : UnitAddCircle, (ε/2)^2 ∂phaseHaar := by
        apply integral_mono
        · exact continuous_circle_integrable
            ((ha.sub (continuous_finsetSum _ (fun k _ => continuous_const.mul (fourier k).continuous))).norm.pow 2)
        · exact integrable_const _
        · intro z
          exact pow_le_pow_left₀ (norm_nonneg _) (hc z).le 2
      _ = _ := by simp
  exact hi.trans_lt (by nlinarith [sq_pos_of_pos hε])

end FinitePacket
end ThreeTorus
end
end

section

/-! The source's reconstruction and prediction survive whitening for the same
finite packet coefficients. The output is a literal Laurent polynomial in the
actual twist, not just membership in an abstract cyclic subspace. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal NNReal Topology BigOperators ComplexConjugate
namespace ThreeTorus
section FinitePacket
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma multiplyPackets_whiten_reconstruct_ae {φ : UnitAddCircle → UnitAddCircle}
    (hφ : Measurable φ) (m : ι → ℤ) {p : UnitAddCircle → ℝ}
    (hp : Measurable p) (hpn : ∀ z, 0 ≤ p z)
    {A V : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i, Measurable (A i))
    (hpush : finitePacketSpectralMeasure φ m A =
      phaseHaar.withDensity (fun z => ENNReal.ofReal (p z))) (D : UnitAddCircle → ℂ) :
    finitePacketVector m (multiplyPackets φ m (fun z => D z*(Real.sqrt (p z):ℂ))
      (whitenPackets φ m p A V)) =ᵐ[tripleVolume]
      finitePacketVector m (multiplyPackets φ m D A) := by
  apply finitePacketVector_congr_ae
  intro i
  filter_upwards [whitenPackets_reconstruct (V := V) hφ m hp hpn hA hpush i] with ua hua
  dsimp only [multiplyPackets]
  rw [mul_assoc,hua]

lemma exists_whitened_laurent_approx {φ : UnitAddCircle → UnitAddCircle}
    (hφ : Measurable φ) {m : ι → ℤ} (hm : Injective m) {p : UnitAddCircle → ℝ}
    (hp : Continuous p) (hpn : ∀ z, 0 ≤ p z)
    {A V : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hVm : ∀ i, Measurable (V i))
    (hpush : finitePacketSpectralMeasure φ m A =
      phaseHaar.withDensity (fun z => ENNReal.ofReal (p z)))
    (hflat : finitePacketSpectralMeasure φ m V = phaseHaar)
    {D : UnitAddCircle → ℂ} (hD : Continuous D) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℤ →₀ ℂ, (∫ x, ‖finitePacketVector m (multiplyPackets φ m D A) x -
      finitePacketLaurent φ m (whitenPackets φ m p A V) c x‖^2 ∂tripleVolume) < ε^2 := by
  have hWm := measurable_whitenPackets hφ m hp.measurable hAm hVm
  have hW := memLp_whitenPackets hφ m hp.measurable hpn hAm hVm hpush hflat
  have hWflat := whitenPackets_flat hφ m hp.measurable hpn hAm hVm hpush hflat
  have hDs : Continuous (fun z => D z*(Real.sqrt (p z):ℂ)) :=
    hD.mul (Complex.continuous_ofReal.comp hp.sqrt)
  obtain ⟨c,hc⟩ := exists_finitePacketLaurent_approx hφ hm hWm hW hWflat hDs hε
  refine ⟨c,?_⟩
  have he := multiplyPackets_whiten_reconstruct_ae (V := V) hφ m hp.measurable hpn hAm hpush D
  have hei : (∫ x, ‖finitePacketVector m (multiplyPackets φ m (fun z => D z*(Real.sqrt (p z):ℂ))
      (whitenPackets φ m p A V)) x - finitePacketLaurent φ m (whitenPackets φ m p A V) c x‖^2
      ∂tripleVolume) = (∫ x, ‖finitePacketVector m (multiplyPackets φ m D A) x -
      finitePacketLaurent φ m (whitenPackets φ m p A V) c x‖^2 ∂tripleVolume) := by
    apply integral_congr_ae
    filter_upwards [he] with x hx
    rw [hx]
  exact hei ▸ hc

lemma whitenPackets_distance_mass {φ : UnitAddCircle → UnitAddCircle}
    (hφ : Measurable φ) {m : ι → ℤ} (hm : Injective m) {p : UnitAddCircle → ℝ}
    (hp : Continuous p) (hpn : ∀ z, 0 ≤ p z)
    {A V : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hVm : ∀ i, Measurable (V i))
    (hA : ∀ i, MemLp (A i) 2 slowVolume)
    (hpush : finitePacketSpectralMeasure φ m A =
      phaseHaar.withDensity (fun z => ENNReal.ofReal (p z)))
    (hflat : finitePacketSpectralMeasure φ m V = phaseHaar) :
    (∫ x, ‖finitePacketVector m (whitenPackets φ m p A V) x-finitePacketVector m A x‖^2
      ∂tripleVolume) = (∫ x, ‖finitePacketVector m A x‖^2 ∂tripleVolume)+1-
        2*(∫ z, Real.sqrt (p z) ∂phaseHaar) := by
  rw [whitenPackets_distance hφ hm hp.measurable hpn hAm hVm hA hpush hflat,
    finitePacket_energy_density hφ hm hAm hA hp.measurable hpn hpush]
  have hpI := continuous_circle_integrable hp
  have hsI := continuous_circle_integrable hp.sqrt
  have he : (fun z => (Real.sqrt (p z)-1)^2) = fun z => p z+1-2*Real.sqrt (p z) := by
    funext z
    nlinarith [Real.sq_sqrt (hpn z)]
  have hsum : Integrable (fun z => p z+1) phaseHaar := hpI.add (integrable_const 1)
  have htwice : Integrable (fun z => 2*Real.sqrt (p z)) phaseHaar := hsI.const_mul 2
  rw [he,integral_sub hsum htwice,
    integral_add hpI (integrable_const 1),integral_const_mul]
  simp

end FinitePacket
end ThreeTorus
end
end

section

/-! The literal flat coefficient, with its two pushforward measures
retained and with an arbitrarily large angular index. This permits adjoining
it to any given finite packet list without changing that list's vector. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal BigOperators ComplexConjugate
namespace ThreeTorus

lemma exists_integer_period_subinterval_above {ψ : ℝ → ℝ} {l u : ℝ}
    (hlu : l < u) (hc : ContinuousOn ψ (Icc l u))
    (hmono : StrictMonoOn ψ (Icc l u)) (B : ℕ) :
    ∃ m : ℕ, B < m ∧ 0 < m ∧ ∃ t ∈ Icc l u, l < t ∧ (m:ℝ)*(ψ t-ψ l) = 1 := by
  have hgap : 0 < ψ u-ψ l := sub_pos.mpr (hmono (left_mem_Icc.mpr hlu.le)
    (right_mem_Icc.mpr hlu.le) hlu)
  obtain ⟨m,hm⟩ := exists_nat_gt (max (1/(ψ u-ψ l)) (B:ℝ))
  have hmB : (B:ℝ) < m := lt_of_le_of_lt (le_max_right _ _) hm
  have hmpos : (0:ℝ) < m := lt_of_le_of_lt (Nat.cast_nonneg B) hmB
  have hmnat : 0 < m := Nat.cast_pos.mp hmpos
  have hsmall : 1/(m:ℝ) < ψ u-ψ l := (one_div_lt hmpos hgap).2
    (lt_of_le_of_lt (le_max_left _ _) hm)
  have hrange : ψ l+1/(m:ℝ) ∈ Icc (ψ l) (ψ u) :=
    ⟨by linarith [one_div_pos.mpr hmpos], by linarith⟩
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc hlu.le hc hrange
  have hlt : l < t := by
    by_contra hh
    have htl : t = l := le_antisymm (le_of_not_gt hh) ht.1
    rw [htl] at he
    linarith [one_div_pos.mpr hmpos]
  refine ⟨m,by exact_mod_cast hmB,hmnat,t,ht,hlt,?_⟩
  rw [he]
  calc
    (m:ℝ)*(ψ l+1/(m:ℝ)-ψ l) = (m:ℝ)*(1/(m:ℝ)) := by ring
    _ = 1 := mul_one_div_cancel (ne_of_gt hmpos)

lemma exists_flat_packet_spectra_above {φ : UnitAddCircle → ℝ} {D : ℝ → ℝ}
    {l u o : ℝ} (hφ : Measurable φ) (hDm : Measurable D) (hlu : l < u)
    (hD : ∀ x ∈ Icc l u, HasDerivWithinAt
      (fun y : ℝ => φ (y : UnitAddCircle)) (D x) (Icc l u) x)
    (hmono : StrictMonoOn (fun y : ℝ => φ (y : UnitAddCircle)) (Icc l u))
    (hi : Icc l u ⊆ Ioc o (o+1)) (B : ℕ) :
    ∃ m : ℕ, B < m ∧ 0 < m ∧ ∃ t ∈ Icc l u, l < t ∧
      let A := fun ua : UnitAddCircle × UnitAddCircle =>
        flatAmplitude o l t (fun x => (m:ℝ)*D x) ua.1
      Measurable A ∧ MemLp A 2 slowVolume ∧ (∀ ua, conj (A ua) = A ua) ∧
      packetSpectralMeasure (fun z => (φ z : UnitAddCircle)) (m:ℤ) A =
        ENNReal.ofReal (1/2:ℝ) • phaseHaar ∧
      packetSpectralMeasure (fun z => (φ z : UnitAddCircle)) (-(m:ℤ)) A =
        ENNReal.ofReal (1/2:ℝ) • phaseHaar ∧
      support A ⊆ ((fun x : ℝ => (x : UnitAddCircle)) '' Icc l t) ×ˢ univ := by
  have hc : ContinuousOn (fun y : ℝ => φ (y : UnitAddCircle)) (Icc l u) :=
    fun x hx => (hD x hx).continuousWithinAt
  obtain ⟨m,hmB,hm,t,ht,hlt,hperiod⟩ := exists_integer_period_subinterval_above hlu hc hmono B
  have hs : Icc l t ⊆ Icc l u := Icc_subset_Icc le_rfl ht.2
  have hmpos : (0:ℝ) < m := Nat.cast_pos.mpr hm
  let φc : UnitAddCircle → UnitAddCircle := fun z => (φ z : UnitAddCircle)
  have hφc : Measurable φc := AddCircle.measurable_mk'.comp hφ
  let Ac : UnitAddCircle → ℂ := flatAmplitude o l t (fun x => (m:ℝ)*D x)
  have hAc : Measurable Ac := measurable_flatAmplitude (measurable_const.mul hDm) o l t
  have hp : (AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal (‖Ac z‖^2))).map
      (fun z => (m:ℤ) • φc z) = ENNReal.ofReal (1/2:ℝ) • phaseHaar := by
    apply flatAmplitude_pushforward (f := fun x : ℝ => (m:ℝ)*φ (x : UnitAddCircle)) hlt.le
      (measurable_const.mul (hφ.comp AddCircle.measurable_mk')) (measurable_const.mul hDm)
    · intro x hx
      exact ((hD x (hs hx)).mono hs).const_mul (m:ℝ)
    · intro x hx y hy hxy
      exact mul_lt_mul_of_pos_left (hmono (hs hx) (hs hy) hxy) hmpos
    · nlinarith
    · exact hs.trans hi
    · exact hφc.const_smul m
    · intro x _
      dsimp only [φc]
      rw [← AddCircle.coe_zsmul,zsmul_eq_mul]
      simp
  have hn := frequency_energy_neg (hφc.const_smul (m:ℤ)) hp
  let : IsFiniteMeasure (ENNReal.ofReal (1/2:ℝ) • phaseHaar) :=
    ⟨by simp only [Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]; finiteness⟩
  have hAcLp := memLp_of_energy_map hAc (hφc.const_smul (m:ℤ)) hp
  refine ⟨m,hmB,hm,t,ht,hlt,hAc.comp measurable_fst,
    hAcLp.comp_measurePreserving measurePreserving_fst,?_,?_,?_,?_⟩
  · intro ua
    simp [flatAmplitude]
  · rw [packetSpectrum_first_coeff hAc hφc]
    exact hp
  · rw [packetSpectrum_first_coeff hAc hφc]
    simpa only [Pi.smul_apply,neg_smul] using hn
  · intro ua hua
    exact ⟨flatAmplitude_support o l t _ hua,mem_univ _⟩

section Padding
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

local instance : MeasurableSingletonClass (ι ⊕ Bool) := by
  constructor
  intro x
  cases x with
  | inl i => simpa only [Set.image_singleton] using (measurableSet_singleton i).inl_image (β := Bool)
  | inr b => simpa only [Set.image_singleton] using (measurableSet_singleton b).inr_image (α := ι)

def paddedAngular (m : ι → ℤ) (k : ℤ) : ι ⊕ Bool → ℤ :=
  Sum.elim m (fun b => if b then k else -k)

def paddedOld (A : ι → UnitAddCircle × UnitAddCircle → ℂ) :
    ι ⊕ Bool → UnitAddCircle × UnitAddCircle → ℂ := Sum.elim A (fun _ _ => 0)

def paddedFlat (V : UnitAddCircle × UnitAddCircle → ℂ) :
    ι ⊕ Bool → UnitAddCircle × UnitAddCircle → ℂ := Sum.elim (fun _ _ => 0) (fun _ => V)

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma paddedAngular_injective {m : ι → ℤ} (hm : Injective m) {k : ℤ} (hk : k ≠ 0)
    (havoid : ∀ i, m i ≠ k ∧ m i ≠ -k) : Injective (paddedAngular m k) := by
  intro x y hxy
  cases x with
  | inl i =>
    cases y with
    | inl j => exact congrArg Sum.inl (hm hxy)
    | inr b => cases b <;> simp_all [paddedAngular]
  | inr b =>
    cases y with
    | inl j =>
      cases b
      · exact False.elim ((havoid j).2 hxy.symm)
      · exact False.elim ((havoid j).1 hxy.symm)
    | inr b' =>
      cases b <;> cases b'
      · rfl
      · change -k = k at hxy
        exact False.elim (hk (by omega))
      · change k = -k at hxy
        exact False.elim (hk (by omega))
      · rfl

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma finitePacketVector_paddedOld (m : ι → ℤ) (k : ℤ)
    (A : ι → UnitAddCircle × UnitAddCircle → ℂ) :
    finitePacketVector (paddedAngular m k) (paddedOld A) = finitePacketVector m A := by
  funext x
  simp [finitePacketVector,Fintype.sum_sum_type,paddedAngular,paddedOld,packet]

lemma finitePacketSpectralMeasure_paddedOld {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (m : ι → ℤ) (k : ℤ) {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i, Measurable (A i)) :
    finitePacketSpectralMeasure φ (paddedAngular m k) (paddedOld A) = finitePacketSpectralMeasure φ m A := by
  rw [finitePacketSpectralMeasure_eq_sum hφ _ (by
    intro i
    cases i with
    | inl j => exact hA j
    | inr _ => exact measurable_const),
    finitePacketSpectralMeasure_eq_sum hφ m hA]
  simp [Fintype.sum_sum_type,paddedAngular,paddedOld,packetSpectralMeasure_zero]

lemma finitePacketSpectralMeasure_paddedFlat {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (m : ι → ℤ) (k : ℤ) {V : UnitAddCircle × UnitAddCircle → ℂ} (hV : Measurable V)
    (hp : packetSpectralMeasure φ k V = ENNReal.ofReal (1/2:ℝ) • phaseHaar)
    (hn : packetSpectralMeasure φ (-k) V = ENNReal.ofReal (1/2:ℝ) • phaseHaar) :
    finitePacketSpectralMeasure φ (paddedAngular m k) (paddedFlat V) = phaseHaar := by
  rw [finitePacketSpectralMeasure_eq_sum hφ _ (by
    intro i
    cases i with
    | inl _ => exact measurable_const
    | inr _ => exact hV)]
  simp only [Fintype.sum_sum_type,paddedAngular,paddedFlat,Sum.elim_inl,Sum.elim_inr,
    packetSpectralMeasure_zero,Finset.sum_const_zero,zero_add,Fintype.sum_bool]
  simp only [Bool.false_eq_true,ite_false,ite_true,hp,hn,← add_smul]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

end Padding
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

lemma density_smooth (r : Fin m) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => C.density r (x:UnitAddCircle)) := by
  classical
  apply ContDiff.sum
  intro i _
  split_ifs <;> first | exact C.packets.density_smooth i | exact contDiff_const

def totalVector (x : TripleTorus) : ℂ := ∑ r, C.vector r x
lemma totalVector_eq (x : TripleTorus) :
    C.totalVector x = ∑ i, packet (C.packets.m i) (C.packets.A i) x := by
  classical
  simp only [totalVector,vector,colorVector]
  rw [Finset.sum_comm]
  simp
lemma totalDensity_eq (z : UnitAddCircle) :
    blockTotal C.density z = ∑ i, C.packets.density i z := by
  classical
  simp only [blockTotal,density,colorDensity]
  rw [Finset.sum_comm]
  simp
lemma totalVector_continuous : Continuous C.totalVector :=
  continuous_finsetSum _ (fun r _ => C.vector_continuous r)

lemma totalVector_spectral_moment (k : ℤ) :
    (∫ x : TripleTorus, conj (C.totalVector x)*C.totalVector
      (twistIter (fun a => (C.packets.periodic.lift a:UnitAddCircle)) k x) ∂tripleVolume) =
      ∫ z, (blockTotal C.density z:ℂ)*fourier k z ∂phaseHaar := by
  have hφ : Continuous (fun a => (C.packets.periodic.lift a:UnitAddCircle)) :=
    (AddCircle.continuous_mk' 1).comp C.packets.speed_continuous
  simp_rw [C.totalVector_eq]
  rw [disjoint_packet_list_correlation C.packets.m C.packets.A
    C.packets.continuous_amplitude hφ (fun i j hij hm => (hij (C.injective hm)).elim) k]
  simp_rw [C.packets.density_spectral C.spare]
  simp_rw [moment_withDensity_real (C.packets.density_continuous _).measurable
    (C.packets.density_nonneg _) (fourier k)]
  simp_rw [C.totalDensity_eq,Complex.ofReal_sum,Finset.sum_mul]
  exact (integral_finsetSum _ (fun i _ =>
    ((Complex.continuous_ofReal.comp (C.packets.density_continuous i)).mul (fourier k).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))).symm

lemma total_mass_energy :
    (∫ z, blockTotal C.density z ∂phaseHaar) =
      ∫ x, ‖C.totalVector x‖^2 ∂tripleVolume := by
  have h := C.totalVector_spectral_moment 0
  have he (x : TripleTorus) :
      conj (C.totalVector x)*C.totalVector (twistIter (fun a => (C.packets.periodic.lift a:UnitAddCircle)) 0 x) =
        ((‖C.totalVector x‖^2:ℝ):ℂ) := by
    simp only [twistIter,zero_zsmul,add_zero]
    rw [mul_comm,Complex.mul_conj,Complex.sq_norm]
  simp_rw [he,fourier_zero,mul_one] at h
  rw [integral_complex_ofReal,integral_complex_ofReal] at h
  exact Complex.ofReal_injective h.symm

lemma exists_center {τR : Fin m → Fin m} (hr : C.Reflection τR) (hτ : Involutive τR)
    {b : Fin m → ℂ} (hb : ∀ r, ‖b r‖ ≤ 1) (hbr : ∀ r, b (τR r) = conj (b r))
    {delta : ℝ} (hd : 0 < delta) :
    ∃ q : UnitAddCircle → ℂ, Continuous q ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => q (x:UnitAddCircle)) ∧
      (∀ z, ‖q z‖ ≤ 2) ∧ (∀ z, q (-z) = conj (q z)) ∧
      (∫ z, Real.sqrt (blockTotal C.density z)*‖blockTagMean C.density b z-q z‖^2 ∂phaseHaar) < delta := by
  apply exists_smooth_symmetric_block_center C.density_nonneg C.density_continuous
    C.density_smooth hb hτ.toPerm _ hbr hd
  intro r z
  simpa using Reflection.density C hr hτ r (-z)

end ColoredState
end ThreeTorus
end
end

section

/-! Literal finite measurable packet states. The spectral measure is defined
from coefficient energy, not carried as an unspecified abstract spectrum. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

structure MeasurablePackets where
  Index : Type
  finite : Fintype Index
  m : Index → ℤ
  injective : Injective m
  nonzero : ∀ i, m i ≠ 0
  A : Index → UnitAddCircle × UnitAddCircle → ℂ
  measurable : ∀ i, Measurable (A i)
  memLp : ∀ i, MemLp (A i) 2 slowVolume

attribute [instance] MeasurablePackets.finite
namespace MeasurablePackets
variable (F : MeasurablePackets)
def vector := finitePacketVector F.m F.A
def spectrum (φ : UnitAddCircle → UnitAddCircle) : Measure UnitAddCircle :=
  ∑ i, packetSpectralMeasure φ (F.m i) (F.A i)

def Reflection (τ : F.Index → F.Index) : Prop :=
  Involutive τ ∧ (∀ i, F.m (τ i) = -F.m i) ∧ ∀ i ua, F.A (τ i) ua = conj (F.A i ua)

def Supported (l u : ℝ) : Prop :=
  ∀ i, support (F.A i) ⊆ ((fun x : ℝ => (x : UnitAddCircle)) '' Icc l u) ×ˢ univ

lemma vector_memLp : MemLp F.vector 2 tripleVolume := memLp_finitePacketVector F.memLp
lemma vector_centered : (∫ x, F.vector x ∂tripleVolume) = 0 :=
  finitePacket_integral_zero F.nonzero F.memLp
lemma vector_real {τ : F.Index → F.Index} (hr : F.Reflection τ) (x : TripleTorus) :
    conj (F.vector x) = F.vector x := finitePacketVector_real τ hr.1 hr.2.1 hr.2.2 x
lemma spectrum_eq [MeasurableSpace F.Index] [MeasurableSingletonClass F.Index]
    {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ) :
    F.spectrum φ = finitePacketSpectralMeasure φ F.m F.A :=
  (finitePacketSpectralMeasure_eq_sum hφ F.m F.measurable).symm

lemma flat_moment {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (hflat : F.spectrum φ = phaseHaar) (n : ℤ) :
    (∫ x, conj (F.vector x)*F.vector (twistIter φ n x) ∂tripleVolume) =
      if n = 0 then 1 else 0 := by
  let : MeasurableSpace F.Index := ⊤
  let : MeasurableSingletonClass F.Index := ⟨fun _ => trivial⟩
  exact finitePacket_flat_moment hφ F.injective F.measurable F.memLp
    ((F.spectrum_eq hφ).symm.trans hflat) n
end MeasurablePackets

namespace ColoredState
variable {n : ℕ} (C : ColoredState (Fin n))
def measurablePackets : MeasurablePackets where
  Index := C.Index
  finite := C.finite
  m := C.packets.m
  injective := C.injective
  nonzero := C.packets.nonzero
  A := C.packets.A
  measurable := fun i => (C.packets.continuous_amplitude i).measurable
  memLp := fun i => (C.packets.continuous_amplitude i).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma measurablePackets_vector : C.measurablePackets.vector = C.totalVector := by
  funext x
  exact (C.totalVector_eq x).symm

lemma measurablePackets_spectrum :
    C.measurablePackets.spectrum (fun u => (C.packets.periodic.lift u:UnitAddCircle)) =
      phaseHaar.withDensity (fun z => ENNReal.ofReal (blockTotal C.density z)) := by
  classical
  change (∑ i, packetSpectralMeasure _ (C.packets.m i) (C.packets.A i)) = _
  simp_rw [C.packets.density_spectral C.spare]
  ext s hs
  rw [Measure.finsetSum_apply,withDensity_apply _ hs]
  simp_rw [withDensity_apply _ hs,C.totalDensity_eq]
  rw [← lintegral_finsetSum]
  · apply lintegral_congr
    intro z
    exact (ENNReal.ofReal_sum_of_nonneg (fun i _ => C.packets.density_nonneg i z)).symm
  · intro i _
    exact (C.packets.density_continuous i).measurable.ennreal_ofReal

lemma totalDensity_even {τR : Fin n → Fin n} (hr : C.Reflection τR)
    (hτR : Involutive τR) (z : UnitAddCircle) :
    blockTotal C.density (-z) = blockTotal C.density z := by
  classical
  unfold blockTotal
  simp_rw [← Reflection.density C hr hτR]
  exact Equiv.sum_comp hτR.toPerm (fun r => C.density r z)

end ColoredState
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

/-- Approximation is chosen on the positive members only; the negative
members are their literal conjugates. Thus reality is exact, not merely AE. -/
lemma exists_reflected_slow_approx (F : MeasurablePackets)
    {τ : F.Index → F.Index} (hr : F.Reflection τ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : F.Index → UnitAddCircle × UnitAddCircle → ℂ,
      (∀ i, Continuous (g i)) ∧
      (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => g i (p.1,p.2))) ∧
      (∀ i p, g (τ i) p = conj (g i p)) ∧
      ∀ i, eLpNorm (fun p => F.A i p-g i p) 2 slowVolume < ENNReal.ofReal ε := by
  classical
  choose a hac has hae using fun i => exists_smooth_slow_approx (F.memLp i) hε
  let g := fun i => if 0 < F.m i then a i else fun p => conj (a (τ i) p)
  have hneg (i : F.Index) (hi : ¬ 0 < F.m i) : 0 < F.m (τ i) := by
    rw [hr.2.1]
    have hn := F.nonzero i
    omega
  refine ⟨g,?_,?_,?_,?_⟩
  · intro i
    dsimp only [g]
    split_ifs
    · exact hac i
    · exact Complex.continuous_conj.comp (hac (τ i))
  · intro i
    dsimp only [g]
    split_ifs
    · exact has i
    · exact Complex.conjCLE.contDiff.comp (has (τ i))
  · intro i p
    by_cases hi : 0 < F.m i
    · have hti : ¬ 0 < F.m (τ i) := by rw [hr.2.1]; omega
      simp [g,hi,hti,hr.1 i]
    · simp [g,hi,hneg i hi]
  · intro i
    by_cases hi : 0 < F.m i
    · simpa only [g,hi,ite_eq_left] using hae i
    · have he : (fun p => F.A i p-g i p) = fun p => conj (F.A (τ i) p-a (τ i) p) := by
        funext p
        simp [g,hi,map_sub,hr.2.2]
      rw [he]
      have hn : eLpNorm (fun p => conj (F.A (τ i) p-a (τ i) p)) 2 slowVolume =
          eLpNorm (fun p => F.A (τ i) p-a (τ i) p) 2 slowVolume :=
        eLpNorm_star
      rw [hn]
      exact hae (τ i)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

/-- Initial smoothing of the SAME supported admissible vector, with exact
reflection and arbitrarily small actual full-space L² error. -/
theorem exists_smooth_reflected_packets (F : MeasurablePackets)
    {τ : F.Index → F.Index} (hr : F.Reflection τ)
    {δ l u : ℝ} (hδ : 0 ≤ δ) (hd : δ < 1/2) (hdl : δ < l) (hud : u < 1-δ)
    (hsupp : F.Supported l u)
    (V : ℝ → ℝ) (hVp : Periodic V 1)
    (hVs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVd : ∀ x ∈ Ioo δ (1-δ), 0 < deriv V x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ G : PassagePackets F.Index, G.m=F.m ∧ G.V=V ∧ G.GoodArc δ ∧
      G.Reflection τ ∧ physicalDist F.vector (finitePacketVector G.m G.A) < ε := by
  classical
  obtain ⟨χ,hχs,hχc,hχI,hχb,hχ1⟩ := compact_smooth_cutoff isCompact_Icc isOpen_Ioo
    (show Icc l u ⊆ Ioo δ (1-δ) from fun x hx => ⟨hdl.trans_le hx.1,hx.2.trans_lt hud⟩)
  have hχsupp : support (fun p : ℝ × UnitAddCircle => χ p.1) ⊆ Ioo (0:ℝ) (0+1) ×ˢ univ := by
    intro p hp
    have h := hχI (subset_tsupport χ hp)
    exact ⟨⟨hδ.trans_lt h.1,by linarith [h.2]⟩,mem_univ _⟩
  have hχone : ∀ p ∈ Icc l u ×ˢ (univ : Set UnitAddCircle), χ p.1 = 1 :=
    fun p hp => (hχ1 p.1 hp.1).self_of_nhds
  have hc : (0:ℝ) < Fintype.card F.Index+1 := by positivity
  obtain ⟨C,hCc,hCs,hCr,hCe⟩ := exists_reflected_slow_approx F hr (div_pos hε hc)
  obtain ⟨G,hGm,hGV,hGd,hGA,hGA₀⟩ := exists_scalar_cutoff_packets F.m F.nonzero C
    hCc hCs hχs hχc hδ hd hχI V hVp hVs hVd
  have hGr : G.Reflection τ := scalar_packets_reflection G hGm hr.2.1 hCr hGA hGA₀
  refine ⟨G,hGm,hGV,hGd,hGr,?_⟩
  have hGl i : MemLp (G.A i) 2 slowVolume := (G.continuous_amplitude i).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hge i : eLpNorm (fun p => F.A i p-G.A i p) 2 slowVolume <
      ENNReal.ofReal (ε/(Fintype.card F.Index+1)) := by
    apply lt_of_le_of_lt
      (eLpNorm_mono ((F.memLp i).aestronglyMeasurable.sub (hGl i).aestronglyMeasurable) ?_)
      (hCe i)
    intro p
    have he := cylinderTorusCutoff_fixes hχsupp (hδ.trans_lt hdl) (by linarith : u < 0+1)
      hχone (hsupp i) p
    rw [cylinderTorusCutoff_scalar] at he
    have hb := cylinderTorusCutoff_bounds hχsupp (fun p => hχb p.1) p
    rw [cylinderTorusCutoff_scalar] at hb
    calc
      _ = ‖((periodize_periodic χ).lift p.1:ℂ)*(F.A i p-C i p)‖ := by
        rw [Pi.sub_apply,hGA,mul_sub,he]
      _ ≤ _ := by
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hb.1]
        exact mul_le_of_le_one_left (norm_nonneg _) hb.2
  rw [hGm]
  exact physicalDist_small_sum F.memLp hGl hε hge

end ThreeTorus
end
end

section

noncomputable section
open Set Function MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

lemma physicalDist_zero_eq_norm {f : TripleTorus → ℂ} (hf : MemLp f 2 tripleVolume) :
    physicalDist f 0 = ‖hf.toLp f‖ := by
  rw [physicalDist_eq_norm hf MemLp.zero]
  simp

namespace MeasurablePackets
variable (F : MeasurablePackets)
lemma flat_norm {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (hflat : F.spectrum φ=phaseHaar) : physicalDist F.vector 0=1 := by
  have hm := F.flat_moment hφ hflat 0
  have hi : (∫ x, ‖F.vector x‖^2 ∂tripleVolume)=1 := by
    have he : (fun x => conj (F.vector x)*F.vector (twistIter φ 0 x)) =
        fun x => ((‖F.vector x‖^2:ℝ):ℂ) := by
      funext x
      simp only [twistIter,zero_smul,add_zero]
      exact normSq_complex (F.vector x)
    rw [he,integral_complex_ofReal] at hm
    simp only [ite_true] at hm
    exact_mod_cast hm
  have hd : physicalDist F.vector 0^2=1 := by
    rw [physicalDist_sq,physicalError]
    simpa only [Pi.zero_apply,sub_zero] using hi
  nlinarith [physicalDist_nonneg F.vector 0]

/-- Smoothing an admissible vector preserves its actual density in L1; the
constant is obtained from the SAME two physical packet vectors. -/
lemma smooth_density_distance (G : PassagePackets F.Index) (hm : G.m=F.m)
    {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (hφG : φ=fun u => (G.periodic.lift u:UnitAddCircle)) (hflat : F.spectrum φ=phaseHaar) :
    (∫ z, |(∑ i, G.marginalDensity i z)-1| ∂phaseHaar) ≤
      (physicalDist (finitePacketVector G.m G.A) 0+1)*
        physicalDist F.vector (finitePacketVector G.m G.A) := by
  let : MeasurableSpace F.Index := ⊤
  let : MeasurableSingletonClass F.Index := ⟨fun _ => trivial⟩
  have hGl i : MemLp (G.A i) 2 slowVolume := (G.continuous_amplitude i).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hGp : finitePacketSpectralMeasure φ F.m G.A =
      phaseHaar.withDensity (fun z => ENNReal.ofReal (∑ i, G.marginalDensity i z)) := by
    rw [← hm,hφG]
    have hψ : Measurable (fun u => (G.periodic.lift u:UnitAddCircle)) :=
      AddCircle.measurable_mk'.comp G.speed_continuous.measurable
    exact (finitePacketSpectralMeasure_eq_sum hψ G.m (fun i => (G.continuous_amplitude i).measurable)).trans
      G.marginalDensity_sum_spectrum
  have hFp : finitePacketSpectralMeasure φ F.m F.A =
      phaseHaar.withDensity (fun _ => ENNReal.ofReal (1:ℝ)) := by
    rw [← F.spectrum_eq hφ,hflat]
    simp
  have he := finitePacket_density_distance hφ F.injective
    (fun i => (G.continuous_amplitude i).measurable) F.measurable hGl F.memLp
    (Finset.measurable_sum _ (fun i _ => G.marginalDensity_measurable i)) measurable_const
    (integrable_finsetSum _ (fun i _ => G.marginalDensity_integrable i)) (integrable_const _)
    (fun z => Finset.sum_nonneg (fun i _ => G.marginalDensity_nonneg i z)) (fun _ => zero_le_one)
    hGp hFp
  rw [← physicalDist_zero_eq_norm (memLp_finitePacketVector hGl),
    ← physicalDist_zero_eq_norm (memLp_finitePacketVector F.memLp)] at he
  change (∫ z, |(∑ i, G.marginalDensity i z)-1| ∂phaseHaar) ≤
      (physicalDist (finitePacketVector F.m G.A) 0+physicalDist F.vector 0)*
        physicalDist (finitePacketVector F.m G.A) F.vector at he
  rw [F.flat_norm hφ hflat,physicalDist_symm _ F.vector] at he
  simpa only [hm] using he
end MeasurablePackets
end ThreeTorus
end
end

section

noncomputable section
open Set Function MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

/-- Source05's full preparation, including both slow insertions. The old
admissible vector and the test are compared in their ACTUAL common chart. -/
theorem exists_prepared_pair (F : MeasurablePackets)
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
    ∃ G H : RealPacketFamily, ∃ α : Equiv.Perm TripleTorus, ∃ frame' : PhysicalFrame,
      Continuous α ∧ MeasurePreserving α tripleVolume tripleVolume ∧
      frame'.chart=frame.chart.trans α ∧ H.data.V=G.data.V ∧ Injective G.data.m ∧
      (∃ δ' : ℝ, 0 < δ' ∧ δ' < 1/8 ∧ δ' < κ ∧ G.data.GoodArc δ' ∧ H.data.GoodArc δ') ∧
      Q.Close ζ frame V frame' G.data.V ∧
      physicalDist F.vector (G.vector ∘ α) < ε ∧
      physicalDist h (H.vector ∘ α) < Real.sqrt (2*δ)+ε ∧
      (∫ z, |G.density z-1| ∂phaseHaar) < ε := by
  classical
  let e := min (ε/16) (1/16)
  have he : 0 < e := lt_min (by positivity) (by norm_num)
  have he1 : e < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have heε : 16*e ≤ ε := by have := min_le_left (ε/16) (1/16); dsimp [e]; linarith
  obtain ⟨P,hPm,hPV,hPg,hPr,hPe⟩ := exists_smooth_reflected_packets F hr hδ hd hdl hud hsupp V hp hs hv he
  let P' : RealPacketFamily := ⟨F.Index,F.finite,P,τ,hr.1,hPr⟩
  have hPi : Injective P'.data.m := hPm ▸ F.injective
  have hφ : Measurable (fun z => (hp.lift z:UnitAddCircle)) :=
    AddCircle.measurable_mk'.comp (continuous_of_continuous_lift (by simpa only [Periodic.lift_coe] using hs.continuous)).measurable
  have hnorm := F.flat_norm hφ hflat
  have hPnorm : physicalDist P'.vector 0 < 1+e := by
    have ht := physicalDist_triangle P'.vector_memLp F.vector_memLp MemLp.zero
    rw [physicalDist_symm P'.vector F.vector,hnorm] at ht
    change physicalDist F.vector P'.vector < e at hPe
    linarith
  have hpD : (∫ z, |P'.density z-1| ∂phaseHaar) < 3*e := by
    have hdens := F.smooth_density_distance P hPm hφ (by
      funext z
      obtain ⟨z,rfl⟩ := Quotient.mk_surjective z
      exact congrArg (fun t : ℝ => (t:UnitAddCircle)) (congrFun hPV z).symm) hflat
    change (∫ z, |P'.density z-1| ∂phaseHaar) ≤
      (physicalDist P'.vector 0+1)*physicalDist F.vector P'.vector at hdens
    have hne : physicalDist P'.vector 0+1 < 3 := by linarith
    have hbd := mul_le_mul_of_nonneg_left hPe.le (by have := Real.sqrt_nonneg (physicalError P'.vector 0); dsimp [physicalDist]; linarith : 0 ≤ physicalDist P'.vector 0+1)
    exact hdens.trans hbd |>.trans_lt (mul_lt_mul_of_pos_right hne he)
  obtain ⟨c,hc0,hcr,H₀,hHV,hHg,hHe⟩ := exists_initial_tensor_test hh hrh hch hbh hδ hd V hp hs hv he
  obtain ⟨G,H,α,frame',hαc,hαm,hfr,hHV',hGi,hgood,hjet,hPF,hHH,hpd⟩ :=
    exists_two_slow_insertions P' H₀ hPi hδ hPg hHg (hHV.trans hPV.symm)
      c hc0 hcr Q frame he hκ hζ
  refine ⟨G,H,α,frame',hαc,hαm,hfr,hHV',hGi,hgood,?_,?_,?_,?_⟩
  · simpa only [show P'.data.V=V from hPV] using hjet
  · exact ((physicalDist_triangle F.vector_memLp P'.vector_memLp
      (continuous_triple_memLp (G.continuous_vector.comp hαc))).trans_lt
      (add_lt_add hPe hPF)).trans_le (by linarith)
  · have ht := physicalDist_triangle (continuous_triple_memLp hh)
      (continuous_triple_memLp ((H₀.continuous_vector.add (tensorPolynomial_continuous (tensorMiddle c))).add (tensorPolynomial_continuous (tensorLast c))))
      (continuous_triple_memLp (H.continuous_vector.comp hαc))
    exact (ht.trans_lt (add_lt_add hHe hHH)).trans_le (by linarith)
  · exact ((densityDist_triangle G.density_integrable P'.density_integrable (integrable_const _)).trans_lt
      (add_lt_add hpd hpD)).trans_le (by linarith)
end ThreeTorus
end
end

section

/-! The two neutral separations retain EACH root color, giving the concrete
input state for predicted blocks. No duplicated angular modes survive. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

theorem exists_colored_separation {n : ℕ} (F : PassagePackets (Fin n))
    (hd : ∀ i j, i ≠ j → F.m i = F.m j → Disjoint (F.cylinderCore i) (F.cylinderCore j))
    (τ : Fin n → Fin n) (hτ : Involutive τ) (hr : F.Reflection τ)
    (Q : PhysicalJetData) (frame : PhysicalFrame)
    {ε κ ζ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hζ : 0 < ζ) :
    ∃ C : ColoredState (Fin n), ∃ α : Equiv.Perm TripleTorus, ∃ frame' : PhysicalFrame,
      Continuous α ∧ MeasurePreserving α tripleVolume tripleVolume ∧
      frame'.chart = frame.chart.trans α ∧ C.Reflection τ ∧
      (∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ C.packets.GoodArc δ) ∧
      Q.Close ζ frame F.V frame' C.packets.V ∧
      ∀ i, physicalError (packet (F.m i) (F.A i)) (C.vector i ∘ α) < ε ∧
        (∫ z, |C.density i z-F.marginalDensity i z| ∂phaseHaar) < ε := by
  classical
  obtain ⟨s,t,hi,hδ,⟨τT,_hτT,hrT,hparent⟩,hjet,herr⟩ :=
    exists_two_neutral_separations F hd τ hτ hr Q frame hε hκ hζ
  let C : ColoredState (Fin n) := {
    Index := PassageOutputIndex t.S
    finite := inferInstance
    packets := t.final
    injective := hi
    spare := t.spare
    color := fun i => i.1.1
    scale := 1
    scale_pos := zero_lt_one }
  have hv (i : Fin n) : C.vector i = pairOutputVector t.final i := by
    funext x
    change colorVector t.final (id ∘ Sigma.fst ∘ Sigma.fst) i x = _
    rw [colorVector_pair]
    simp
  have hp (i : Fin n) : C.density i = pairOutputDensity t.final i := by
    funext z
    change colorDensity t.final (id ∘ Sigma.fst ∘ Sigma.fst) i z = _
    rw [colorDensity_pair]
    simp
  refine ⟨C,s.chart.trans t.chart,t.nextFrame (s.nextFrame frame),?_,?_,?_,?_,?_,hjet,?_⟩
  · exact (continuous_passageChart (t.geometry.Hcontinuous t.n)).comp
      (continuous_passageChart (s.geometry.Hcontinuous s.n))
  · exact (measurePreserving_passageChart (t.geometry.Hcontinuous t.n).measurable).comp
      (measurePreserving_passageChart (s.geometry.Hcontinuous s.n).measurable)
  · rfl
  · exact ⟨τT,hrT,hparent⟩
  · exact ⟨t.δ,t.δpos,t.δsmall,hδ,t.good⟩
  · intro i
    rw [hv,hp]
    exact herr i

end ThreeTorus
end
end

end OAI
