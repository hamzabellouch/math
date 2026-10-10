import OAI.Analysis.LipschitzHilbert.Geometry.SourceTransverseTreeVariation

namespace OAI

/-! Transverse polynomial energy for the actual interval maximum,
including finite label slots, from the published scalar Lépingle input. -/
noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform ENNReal NNReal
namespace LipschitzHilbert

private theorem interval_max_le_variation {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N : ℕ) : intervalOscillation F N 0 N≤cubicVariation F N := by
  obtain ⟨a,b,_,hab,hb,heq⟩ := exists_intervalOscillation_eq F N 0 N (Nat.zero_le _)
  rw [heq]
  exact increment_le_cubicVariation F N a b hab hb

private theorem interval_max_sum_le {I E : Type*} [Fintype I] [NormedAddCommGroup E]
    (F : I → ℕ → E) (N : ℕ) :
    intervalOscillation (fun n => ∑ i, F i n) N 0 N≤
      ∑ i, intervalOscillation (F i) N 0 N := by
  classical
  unfold intervalOscillation
  apply Finset.sup'_le
  intro q _
  split_ifs with hq
  · rw [←Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    exact increment_le_intervalOscillation (F i) N 0 N q.1 q.2
      (Nat.zero_le _) hq.2.1 hq.2.2 le_rfl
  · exact Finset.sum_nonneg fun i _ => intervalOscillation_nonneg (F i) N 0 N

namespace SourceLatticePacket

theorem exists_transverse_physical_tree_maximal (hL : LepingleInput)
    (cStar cEta CEta cb Cb : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hcb : 0≤cb) (hCb : 0≤Cb) (hgap : cStar<cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι)
      (t w b : ℝ), 0<w → 207≤P.order →
    ∀ c : ∀ j, ι j → EuclideanSpace ℂ κ,
      (∀ j u, |P.actualZ j u-b|≤P.width) →
      (∀ j u k ξ η, planarAngularFourier (P.physicalPacket t j u k) (ξ,η)≠0 →
        |ξ+(t+P.rowSlope j)*η|≤cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ j (_u : ι j), cb*w/P.length j≤|P.rowSlope j| ∧
        |P.rowSlope j|≤Cb*w/P.length j) →
      let E := fun z => polynomialWeight b (2*P.width) 103 (z.2-t*z.1)^2 *
        P.physicalTreeMaximal t c z^2
      Integrable E (volume.prod volume) ∧
      (∫ z, E z ∂volume.prod volume)≤C*P.absoluteConstant^2 *
        ∑ j, ∑ u, ‖c j u‖^2*P.length j*P.width := by
  obtain ⟨C,hC,hbound⟩ := exists_transverse_physical_tree_variation hL
    cStar cEta CEta cb Cb hcStar hcEta hCEta hcb hCb hgap
  refine ⟨C,hC,?_⟩
  intro N κ ι _ _ P t w b hw horder c hZ hspectrum hselector
  obtain ⟨hi,hb⟩ := hbound N κ ι P t w b hw horder c hZ hspectrum hselector
  have hp (z : ℝ×ℝ) : P.physicalTreeMaximal t c z≤P.physicalTreeVariation t c z :=
    interval_max_le_variation _ N
  have hle (z : ℝ×ℝ) : polynomialWeight b (2*P.width) 103 (z.2-t*z.1)^2*P.physicalTreeMaximal t c z^2≤
      polynomialWeight b (2*P.width) 103 (z.2-t*z.1)^2*P.physicalTreeVariation t c z^2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (intervalOscillation_nonneg _ _ _ _) (hp z) 2) (sq_nonneg _)
  have hc : Continuous (fun z => polynomialWeight b (2*P.width) 103 (z.2-t*z.1)^2*P.physicalTreeMaximal t c z^2) := by
    have hwc : Continuous (fun z : ℝ×ℝ => polynomialWeight b (2*P.width) 103 (z.2-t*z.1)) := by
      unfold polynomialWeight; fun_prop
    exact (hwc.pow 2).mul ((P.physicalTreeMaximal_continuous t c).pow 2)
  have him : Integrable (fun z => polynomialWeight b (2*P.width) 103 (z.2-t*z.1)^2*P.physicalTreeMaximal t c z^2)
      (volume.prod volume) := hi.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg (polynomialWeight b (2*P.width) 103 (z.2-t*z.1)))
          (sq_nonneg (P.physicalTreeMaximal t c z)))] using hle z)
  exact ⟨him,(integral_mono him hi hle).trans hb⟩

end SourceLatticePacket

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
attribute [local instance] Classical.propDecidable

theorem exists_transverse_labeled_tree_maximal (hL : LepingleInput)
    (cStar cEta CEta cb Cb : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hcb : 0≤cb) (hCb : 0≤Cb) (hgap : cStar<cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (B : ℕ),
      (∀ j, (P.labels j).card≤B) → ∀ (t w b : ℝ), 0<w → 207≤P.order →
    ∀ c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ,
      (∀ j l u, |P.actualZ j l u-b|≤P.width) →
      (∀ j l u k ξ η, planarAngularFourier (P.physicalPacket t j l u k) (ξ,η)≠0 →
        |ξ+(t+P.rowSlope j l)*η|≤cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ j (l : P.labels j) (_u : Item j l), cb*w/P.length j≤|P.rowSlope j l| ∧
        |P.rowSlope j l|≤Cb*w/P.length j) →
      let E := fun z => polynomialWeight b (2*P.width) 103 (z.2-t*z.1)^2 *
        P.physicalTreeMaximal t c z^2
      Integrable E (volume.prod volume) ∧
      (∫ z, E z ∂volume.prod volume)≤(B:ℝ)*C*P.absoluteConstant^2 *
        ∑ j, ∑ l : P.labels j, ∑ u : Item j l, ‖c j l u‖^2*P.length j*P.width := by
  obtain ⟨C,hC,hbound⟩ := SourceLatticePacket.exists_transverse_physical_tree_maximal hL
    cStar cEta CEta cb Cb hcStar hcEta hCEta hcb hCb hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P B hcard t w b hw horder c hZ hspectrum hselector
  let weight := fun z : ℝ×ℝ => polynomialWeight b (2*P.width) 103 (z.2-t*z.1)
  let coeff := fun (s : Fin B) j (u : P.SlotItem hcard s j) => c j u.1.1 u.1.2
  let M := fun s : Fin B => (P.slotted hcard s).physicalTreeMaximal t (coeff s)
  let mass := fun s : Fin B => ∑ j, ∑ u : P.SlotItem hcard s j,
    ‖coeff s j u‖^2*P.length j*P.width
  have hslot (s : Fin B) : Integrable (fun z => weight z^2*M s z^2) (volume.prod volume) ∧
      (∫ z, weight z^2*M s z^2 ∂volume.prod volume)≤C*P.absoluteConstant^2*mass s := by
    apply hbound N κ (P.SlotItem hcard s) (P.slotted hcard s) t w b hw horder (coeff s)
    · intro j u
      change |(P.slotted hcard s).actualZ j u-b|≤P.width
      simpa only [P.slotted_actualZ hcard] using hZ j u.1.1 u.1.2
    · exact P.slotted_spectrum hcard t w cStar cEta CEta hspectrum s
    · intro j u
      simpa only [P.slotted_length hcard,P.slotted_rowSlope hcard s j u] using
        hselector j u.1.1 u.1.2
  have hpartial (n : ℕ) (z : ℝ×ℝ) :
      (∑ s : Fin B, (P.slotted hcard s).physicalTreePartial t (coeff s) n z)=
        P.physicalTreePartial t c n z := by
    simp only [SourceLatticePacket.physicalTreePartial,physicalTreePartial,packetPartialSum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.val<n
    · simp only [ite_eq_left hj]
      ext k
      simp only [planarFixedSynthesis,WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_toLp,
        P.slotted_physicalPacket hcard,coeff]
      simpa only [Fintype.sum_sigma] using P.sum_slotted hcard j
        (fun l u => c j l u k*P.physicalPacket t j l u k z)
    · simp only [ite_eq_right hj,Finset.sum_const_zero]
  have hmax (z : ℝ×ℝ) : P.physicalTreeMaximal t c z≤∑ s, M s z := by
    have heq : (fun n => P.physicalTreePartial t c n z)=
        (fun n => ∑ s : Fin B, (P.slotted hcard s).physicalTreePartial t (coeff s) n z) :=
      funext fun n => (hpartial n z).symm
    unfold physicalTreeMaximal
    rw [heq]
    exact interval_max_sum_le _ N
  have hwc : Continuous weight := by
    dsimp only [weight]
    unfold polynomialWeight
    fun_prop
  have hM0 (s : Fin B) (z : ℝ×ℝ) : 0≤M s z := intervalOscillation_nonneg _ _ _ _
  have hM2 (s : Fin B) : MemLp (fun z => weight z*M s z) 2 (volume.prod volume) := by
    have hm : AEStronglyMeasurable (fun z => weight z*M s z) (volume.prod volume) :=
      (hwc.mul ((P.slotted hcard s).physicalTreeMaximal_continuous t (coeff s))).aestronglyMeasurable
    apply (memLp_two_iff_integrable_sq hm).2
    simpa only [mul_pow] using (hslot s).1
  have hsum2 := memLp_finsetSum Finset.univ (fun s _ => hM2 s)
  have hsumI := hsum2.integrable_norm_pow (by decide : 2≠0)
  have hcost := weighted_integral_sum_square (volume.prod volume)
    (fun s z => weight z*M s z) hM2 (fun _ => (1:ℝ)) (fun _ => by norm_num)
  simp only [div_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hcost
  have hpoint (z : ℝ×ℝ) : weight z^2*P.physicalTreeMaximal t c z^2≤
      ‖∑ s, weight z*M s z‖^2 := by
    rw [←Finset.mul_sum,Real.norm_eq_abs,sq_abs,mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀
      (intervalOscillation_nonneg _ _ _ _) (hmax z) 2) (sq_nonneg _)
  have hE : Integrable (fun z => weight z^2*P.physicalTreeMaximal t c z^2) (volume.prod volume) := by
    apply hsumI.mono'
      ((hwc.pow 2).mul ((P.physicalTreeMaximal_continuous t c).pow 2)).aestronglyMeasurable
    filter_upwards [] with z
    change ‖weight z^2*P.physicalTreeMaximal t c z^2‖ ≤ ‖∑ s, weight z*M s z‖^2
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg (weight z))
      (sq_nonneg (P.physicalTreeMaximal t c z)))]
    exact hpoint z
  have hmass : (∑ s, mass s)=
      ∑ j, ∑ l : P.labels j, ∑ u : Item j l, ‖c j l u‖^2*P.length j*P.width := by
    dsimp only [mass,coeff]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact P.sum_slotted hcard j (fun l u => ‖c j l u‖^2*P.length j*P.width)
  refine ⟨hE,(integral_mono hE hsumI hpoint).trans (hcost.trans ?_)⟩
  simp only [Real.norm_eq_abs,mul_pow,sq_abs]
  calc
    _ ≤ (B:ℝ)*∑ s, C*P.absoluteConstant^2*mass s :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _ => (hslot s).2) (Nat.cast_nonneg B)
    _ = _ := by rw [←Finset.mul_sum,hmass]; ring

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
