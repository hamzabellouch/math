import Mathlib
import OAI.Computability.QuantumFactoring.InitialOrderState
import OAI.Computability.QuantumFactoring.OrderTrialLaw

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork Exactness
namespace OrderTrial

/-- Distinct powers in one period; this is an embedding, not an oracle for r. -/
def powerOrbit {G : Type*} [Group G] (a : G) : Fin (orderOf a)→G := fun t => a^t.val
lemma powerOrbit_injective {G : Type*} [Group G] (a : G) : Function.Injective (powerOrbit a) := by
  intro s t h
  apply Fin.ext
  exact pow_injOn_Iio_orderOf s.isLt t.isLt h

lemma selectedSampleAmplitude_outside {G : Type*} [Group G] [Finite G]
    (Q k : ℕ) (a u : G) (hu : u ∉ Set.range (powerOrbit a)) :
    selectedSampleAmplitude Q k a u=0 := by
  have h : ∀ x : ℕ, a^x≠u := by
    intro x hx
    apply hu
    refine ⟨⟨x%orderOf a,Nat.mod_lt _ (orderOf_pos a)⟩,?_⟩
    exact (pow_mod_orderOf a x).trans hx
  simp [selectedSampleAmplitude,h]

lemma selectedSampleProbability_sum {G : Type*} [Group G] [Fintype G]
    (Q j : ℕ) (a : G) :
    (∑ u : G, Complex.normSq (selectedSampleAmplitude Q (bin Q (orderOf a) j) a u))=
      ∑ t : Fin (orderOf a), residueProbability Q (orderOf a) j t.val := by
  classical
  let e := powerOrbit a
  have he : Function.Injective e := powerOrbit_injective a
  have hz : ∀ u ∈ (Finset.univ : Finset G), u∉Finset.univ.image e →
      Complex.normSq (selectedSampleAmplitude Q (bin Q (orderOf a) j) a u)=0 := by
    intro u _ hu
    rw [selectedSampleAmplitude_outside Q _ a u]
    · exact map_zero _
    · rintro ⟨t,rfl⟩
      exact hu (Finset.mem_image.mpr ⟨t,Finset.mem_univ _,rfl⟩)
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e)) hz,
    Finset.sum_image (fun _ _ _ _ h => he h)]
  apply Finset.sum_congr rfl
  intro t _
  exact selectedSampleProbability_residue Q j a t.isLt

/-- Exact bit representation used for modular-power values. -/
def natBasis (w z : ℕ) : Basis w := fun i => (BitVec.ofNat w z).getLsbD i.val
lemma natBasis_value (w z : ℕ) : (bitsValue (natBasis w z)).toNat=z%2^w := by
  change (bitsValue (fun i : Fin w => (BitVec.ofNat w z).getLsbD i.val)).toNat=z%2^w
  exact congrArg BitVec.toNat (bitsValue_bits (BitVec.ofNat w z))
lemma natBasis_injectiveOn (w : ℕ) : Set.InjOn (natBasis w) (Set.Iio (2^w)) := by
  intro x hx y hy h
  have hh := congrArg (fun z : Basis w => (bitsValue z).toNat) h
  simpa only [natBasis_value,Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hy] using hh

/-- Embed all units into the physical modular-power register, when m<2^w. -/
def unitWord {m w : ℕ} (u : (ZMod m)ˣ) : Basis w := natBasis w (u : ZMod m).val
lemma unitWord_value {m w : ℕ} [NeZero m] (hm : m<2^w) (u : (ZMod m)ˣ) :
    (bitsValue (unitWord (w:=w) u)).toNat=(u : ZMod m).val := by
  rw [unitWord,natBasis_value,Nat.mod_eq_of_lt ((ZMod.val_lt _).trans hm)]
lemma unitWord_injective {m w : ℕ} [NeZero m] (hm : m<2^w) :
    Function.Injective (unitWord (m:=m) (w:=w)) := by
  intro u v h
  apply Units.ext
  apply ZMod.val_injective
  have hh := congrArg (fun x : Basis w => (bitsValue x).toNat) h
  simpa only [unitWord_value hm] using hh

lemma nat_pow_eq_unit {m a : ℕ} [NeZero m] (u : (ZMod m)ˣ)
    (ha : (a : ZMod m)=(u : ZMod m)) (x : ℕ) :
    a^x%m=((u^x : (ZMod m)ˣ) : ZMod m).val := by
  rw [Units.val_pow_eq_pow_val,← ha,← Nat.cast_pow,ZMod.val_natCast]

lemma nat_pow_eq_word_iff {m w a : ℕ} [NeZero m] (hm : m<2^w)
    (u v : (ZMod m)ˣ) (ha : (a : ZMod m)=(u : ZMod m)) (x : ℕ) :
    a^x%m=(bitsValue (unitWord (w:=w) v)).toNat ↔ u^x=v := by
  rw [unitWord_value hm,nat_pow_eq_unit u ha]
  exact ⟨fun h => Units.ext (ZMod.val_injective _ h),fun h => by rw [h]⟩

/-- The physical amplitude, at any encoded unit, equals the group-theoretic
coherent residue sum. No early classical measurement is used here. -/
theorem sampler_unit_amplitude {w s : ℕ} (a m : Basis w) (y : Basis (s+2))
    (hm : 2≤(bitsValue m).toNat) (u v : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat)) :
    (programMatrix (OrderSample.completeSampler w s)).mulVec
      (basisVector (OrderSample.word a m (fun _=>false) (fun _=>false)))
      (OrderSample.word a m y (unitWord (w:=w) v))=
      selectedSampleAmplitude (2^(s+2)) (Triangular.outputNumber y) u v := by
  let : NeZero (bitsValue m).toNat := ⟨by omega⟩
  rw [OrderSample.completeSampler_amplitude _ _ _ _ hm]
  simp only [selectedSampleAmplitude,nat_pow_eq_word_iff (bitsValue m).isLt u v ha]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> rfl


lemma outcomeMass_range {α β : Type*} [Fintype α] [Fintype β]
    (e : α→β) (he : Function.Injective e) (ψ : β→ℂ) :
    outcomeMass (fun y => y∈Set.range e) ψ=∑ a, Complex.normSq (ψ (e a)) := by
  classical
  let f : β→ℝ := fun y => if y∈Set.range e then Complex.normSq (ψ y) else 0
  have hh : outcomeMass (fun y => y∈Set.range e) ψ=Finset.univ.sum f := by
    unfold outcomeMass
    apply Finset.sum_congr rfl
    intro y _
    dsimp only [f]
    split_ifs <;> rfl
  rw [hh]
  have hz : ∀ y∈(Finset.univ : Finset β), y∉Finset.univ.image e → f y=0 := by
    intro y _ hy
    dsimp only [f]
    rw [ite_eq_right]
    rintro ⟨a,rfl⟩
    exact hy (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e)) hz,
    Finset.sum_image (fun _ _ _ _ h => he h)]
  apply Finset.sum_congr rfl
  intro t _
  exact ite_eq_left ⟨t,rfl⟩

lemma sampler_word_injective {w b : ℕ} (a m : Basis w) (y : Basis b) :
    Function.Injective (OrderSample.word a m y) := by
  intro u v h
  have hh := BooleanNetwork.packed_injective
    (a₁:=(OrderSample.inputWord a m y,u)) (a₂:=(OrderSample.inputWord a m y,v)) h
  exact congrArg Prod.snd hh

noncomputable def samplerState {w s : ℕ} (a m : Basis w) : State (OrderSample.width w (s+2)) :=
  (programMatrix (OrderSample.completeSampler w s)).mulVec
    (basisVector (OrderSample.word a m (fun _=>false) (fun _=>false)))

lemma sampler_outside_units {w s : ℕ} (a m : Basis w) (y : Basis (s+2))
    (hm : 2≤(bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (z : Basis w) (hz : z∉Set.range (unitWord (m:=(bitsValue m).toNat) (w:=w))) :
    samplerState a m (OrderSample.word a m y z)=0 := by
  let : NeZero (bitsValue m).toNat := ⟨by omega⟩
  have hh : ∀ x : ℕ, (bitsValue a).toNat^x%(bitsValue m).toNat≠(bitsValue z).toNat := by
    intro x hx
    apply hz
    refine ⟨u^x,?_⟩
    apply (bitsEquiv w).injective
    apply BitVec.eq_of_toNat_eq
    change (bitsValue (unitWord (w:=w) (u^x))).toNat=(bitsValue z).toNat
    rw [unitWord_value (bitsValue m).isLt,← nat_pow_eq_unit u ha]
    exact hx
  rw [samplerState,OrderSample.completeSampler_amplitude _ _ _ _ hm]
  simp only [hh,ite_false,Finset.sum_const_zero,mul_zero]

/-- The complete physical selected-bin probability is the sum of the literal
residue probabilities at the TRUE order. False labels are not identified with
artificial probabilities. -/
theorem sampler_selected_bin_mass {w s : ℕ} (a m : Basis w) (y : Basis (s+2))
    (hm : 2≤(bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (j : ℕ) (hy : Triangular.outputNumber y=bin (2^(s+2)) (orderOf u) j) :
    outcomeMass (fun z => z∈Set.range (OrderSample.word a m y)) (samplerState a m)=
      ∑ t : Fin (orderOf u), residueProbability (2^(s+2)) (orderOf u) j t.val := by
  classical
  let : NeZero (bitsValue m).toNat := ⟨by omega⟩
  rw [outcomeMass_range _ (sampler_word_injective a m y)]
  let e := unitWord (m:=(bitsValue m).toNat) (w:=w)
  have he : Function.Injective e := unitWord_injective (bitsValue m).isLt
  have hz : ∀ z∈(Finset.univ : Finset (Basis w)), z∉Finset.univ.image e →
      Complex.normSq (samplerState a m (OrderSample.word a m y z))=0 := by
    intro z _ hz
    rw [sampler_outside_units a m y hm u ha z]
    · exact map_zero _
    · rintro ⟨v,rfl⟩
      exact hz (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩)
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e)) hz,
    Finset.sum_image (fun _ _ _ _ h => he h)]
  simp only [e,samplerState,sampler_unit_amplitude a m y hm u _ ha,hy]
  exact selectedSampleProbability_sum _ j u

end OrderTrial
end ExactQuantumFactoring


end

end OAI
