import OAI.MathematicalPhysics.Heisenberg.HittingEnergy

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open scoped BigOperators Classical
open scoped Classical
open scoped Classical
open Filter

open scoped Classical
namespace Heisenberg.Return
open Equiv
variable {V : Type*}

def HasHit (π : Perm V) (P : Set V) (x : V) : Prop := ∃ n : ℕ, (π ^ n) x ∈ P

lemma hasHit_iff_cycle [Fintype V] (π : Perm V) (P : Set V) (x : V) :
    HasHit π P x ↔ ∃ p ∈ P, π.SameCycle x p := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨(π ^ n) x, hn, (Perm.SameCycle.refl π x).pow_right⟩
  · rintro ⟨p, hp, hc⟩
    obtain ⟨n, hn⟩ := hc.exists_nat_pow_eq
    exact ⟨n, hn ▸ hp⟩

lemma hasHit_apply [Fintype V] (π : Perm V) (P : Set V) (x : V) :
    HasHit π P (π x) ↔ HasHit π P x := by
  simp only [hasHit_iff_cycle, Perm.sameCycle_apply_left]

lemma hasHit_of_mem (π : Perm V) {P : Set V} {x : V} (hx : x ∈ P) : HasHit π P x :=
  ⟨0, hx⟩

def hitTime (π : Perm V) (P : Set V) (x : V) (h : HasHit π P x) := Nat.find h

def hitPoint (π : Perm V) (P : Set V) (x : V) (h : HasHit π P x) : V :=
  (π ^ hitTime π P x h) x

lemma hitPoint_mem (π : Perm V) (P : Set V) (x : V) (h : HasHit π P x) :
    hitPoint π P x h ∈ P := Nat.find_spec h

lemma hitTime_le (π : Perm V) (P : Set V) (x : V) (h : HasHit π P x)
    {n : ℕ} (hn : (π ^ n) x ∈ P) : hitTime π P x h ≤ n := Nat.find_min' h hn

lemma hitTime_zero (π : Perm V) (P : Set V) (x : V) (h : HasHit π P x)
    (hx : x ∈ P) : hitTime π P x h = 0 := by
  exact Nat.eq_zero_of_le_zero (hitTime_le π P x h (n := 0) hx)

lemma hitTime_pos (π : Perm V) (P : Set V) (x : V) (h : HasHit π P x)
    (hx : x ∉ P) : 0 < hitTime π P x h := by
  by_contra hn
  have he : hitTime π P x h = 0 := by omega
  have hm := hitPoint_mem π P x h
  exact hx (by simpa [hitPoint, he] using hm)

variable [Fintype V]

lemma hitTime_step (π : Perm V) (P : Set V) (x : V) (h : HasHit π P x)
    (hx : x ∉ P) :
    hitTime π P x h = hitTime π P (π x) ((hasHit_apply π P x).mpr h) + 1 := by
  have hm := hitPoint_mem π P (π x) ((hasHit_apply π P x).mpr h)
  have hp := hitTime_pos π P x h hx
  apply Nat.le_antisymm
  · apply hitTime_le
    simpa only [hitPoint, pow_succ, Perm.mul_apply] using hm
  · have he : (π ^ (hitTime π P x h - 1)) (π x) ∈ P := by
      rw [← Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel hp]
      exact hitPoint_mem π P x h
    have hl := hitTime_le π P (π x) ((hasHit_apply π P x).mpr h) he
    omega

def firstValue (π : Perm V) (P : Set V) (x : V) : Option V :=
  if h : HasHit π P x then some (hitPoint π P x h) else none

omit [Fintype V] in
lemma firstValue_of_mem (π : Perm V) {P : Set V} {x : V} (hx : x ∈ P) :
    firstValue π P x = some x := by
  have h := hasHit_of_mem π hx
  simp [firstValue, h, hitPoint, hitTime_zero π P x h hx]

lemma firstValue_step (π : Perm V) (P : Set V) (x : V) (hx : x ∉ P) :
    firstValue π P (π x) = firstValue π P x := by
  by_cases h : HasHit π P x
  · have h' := (hasHit_apply π P x).mpr h
    simp only [firstValue, dite_eq_left h, dite_eq_left h']
    congr 1
    simp only [hitPoint, hitTime_step π P x h hx, pow_succ, Perm.mul_apply]
  · have h' : ¬ HasHit π P (π x) := by simpa only [hasHit_apply] using h
    simp [firstValue, h, h']

lemma harmonic_firstHit {W : Type*} (π : Perm V) (P : Set V) (g : V → W)
    (hg : ∀ x ∉ P, g (π x) = g x) (x : V) (h : HasHit π P x) :
    g (hitPoint π P x h) = g x := by
  have hn (n : ℕ) : ∀ x (h : HasHit π P x), hitTime π P x h = n →
      g (hitPoint π P x h) = g x := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x h he
      by_cases hx : x ∈ P
      · simp [hitPoint, hitTime_zero π P x h hx]
      · have ht := hitTime_step π P x h hx
        have hl : hitTime π P (π x) ((hasHit_apply π P x).mpr h) < n := by omega
        have hr := ih _ hl (π x) ((hasHit_apply π P x).mpr h) rfl
        rw [hitPoint, ht, pow_succ, Perm.mul_apply]
        exact hr.trans (hg x hx)
  exact hn _ x h rfl

lemma firstValue_unique {W : Type*} (π : Perm V) (P : Set V)
    (g : V → Option W) (b : V → W)
    (hb : ∀ x ∈ P, g x = some (b x))
    (hg : ∀ x ∉ P, g (π x) = g x)
    (x : V) (h : HasHit π P x) :
    g x = (firstValue π P x).map b := by
  rw [firstValue, dite_eq_left h]
  exact (harmonic_firstHit π P g hg x h).symm.trans
    (hb _ (hitPoint_mem π P x h))

lemma firstValue_splice_step (π : Perm (Option V)) (P : Set V) (i : V) :
    firstValue π (some '' P) (some (removeNone π i)) =
      firstValue π (some '' P) (π (some i)) := by
  cases h : π (some i) with
  | none =>
    rw [removeNone_none π h]
    exact firstValue_step π (some '' P) none (by simp)
  | some j =>
    rw [removeNone_some π ⟨j, h⟩, h]

lemma firstValue_spliced_harmonic (π : Perm (Option V)) (P : Set V) :
    ∀ i ∉ P, firstValue π (some '' P) (some (removeNone π i)) =
      firstValue π (some '' P) (some i) := by
  intro i hi
  rw [firstValue_splice_step]
  exact firstValue_step π _ _ (by simpa using hi)

theorem nextValue_splice (π : Perm (Option V)) (P : Set V) (i : V) (hi : i ∈ P) :
    firstValue π (some '' P) (π (some i)) =
      (firstValue (removeNone π) P (removeNone π i)).map some := by
  rw [← firstValue_splice_step]
  apply firstValue_unique (removeNone π) P
    (fun i => firstValue π (some '' P) (some i)) some
  · intro i hi
    exact firstValue_of_mem π ⟨i, hi, rfl⟩
  · exact firstValue_spliced_harmonic π P
  · exact (hasHit_apply (removeNone π) P i).mpr (hasHit_of_mem _ hi)

def nextTime (π : Perm V) (P : Set V) (i : P) : ℕ :=
  hitTime π P (π i) ((hasHit_apply π P i).mpr (hasHit_of_mem π i.property)) + 1

def nextPoint (π : Perm V) (P : Set V) (i : P) : P :=
  ⟨hitPoint π P (π i) ((hasHit_apply π P i).mpr (hasHit_of_mem π i.property)),
    hitPoint_mem π P _ _⟩

lemma nextTime_pos (π : Perm V) (P : Set V) (i : P) : 0 < nextTime π P i := Nat.succ_pos _

lemma nextPoint_spec (π : Perm V) (P : Set V) (i : P) :
    (π ^ nextTime π P i) i = (nextPoint π P i : V) := by
  simp only [nextTime, nextPoint, hitPoint, pow_succ, Perm.mul_apply]

lemma nextTime_min (π : Perm V) (P : Set V) (i : P) {n : ℕ}
    (hn : 0 < n) (hp : (π ^ n) i ∈ P) : nextTime π P i ≤ n := by
  have he : (π ^ (n - 1)) (π i) ∈ P := by
    rw [← Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel hn]
    exact hp
  have hm := hitTime_le π P (π i) ((hasHit_apply π P i).mpr (hasHit_of_mem π i.property)) he
  exact Nat.succ_le_of_lt (lt_of_le_of_lt hm (Nat.sub_lt hn (by omega)))

lemma nextPoint_injective (π : Perm V) (P : Set V) : Function.Injective (nextPoint π P) := by
  have haux (i j : P) (hn : nextTime π P i ≤ nextTime π P j)
      (he : nextPoint π P i = nextPoint π P j) : i = j := by
    let n := nextTime π P i
    let m := nextTime π P j
    have hn0 : 0 < n := nextTime_pos π P i
    have hm0 : 0 < m := nextTime_pos π P j
    have hb : (π ^ (m - n)) (j : V) = (i : V) := by
      apply (π ^ n).injective
      calc
        (π ^ n) ((π ^ (m - n)) (j : V)) = (π ^ m) (j : V) := by
          rw [← Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hn]
        _ = (nextPoint π P j : V) := nextPoint_spec π P j
        _ = (nextPoint π P i : V) := congrArg Subtype.val he.symm
        _ = (π ^ n) (i : V) := (nextPoint_spec π P i).symm
    have hz : m - n = 0 := by
      by_contra hne
      have ht := nextTime_min π P j (Nat.pos_of_ne_zero hne) (hb ▸ i.property)
      change m ≤ m - n at ht
      omega
    apply Subtype.ext
    simpa only [hz, pow_zero, Perm.one_apply] using hb.symm
  intro i j he
  rcases le_total (nextTime π P i) (nextTime π P j) with hle | hle
  · exact haux i j hle he
  · exact (haux j i hle he.symm).symm

def nextPermutation (π : Perm V) (P : Set V) : Perm P :=
  Equiv.ofBijective (nextPoint π P) ((Finite.injective_iff_bijective).mp (nextPoint_injective π P))

lemma nextValue_eq_nextPoint (π : Perm V) (P : Set V) (i : P) :
    firstValue π P (π i) = some (nextPoint π P i : V) := by
  rw [firstValue, dite_eq_left ((hasHit_apply π P i).mpr (hasHit_of_mem π i.property))]
  rfl

end Heisenberg.Return

namespace Heisenberg.Exposure
open Heisenberg.Return
variable {V : Type*} [Fintype V]

lemma semiconj_perm_pow {X Y : Type*} (f : X → Y) (π : Equiv.Perm X) (σ : Equiv.Perm Y)
    (hf : ∀ x,f (π x)=σ (f x)) (n : ℕ) (x : X) : f ((π^n) x)=(σ^n) (f x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ',Equiv.Perm.mul_apply,hf,ih,pow_succ',Equiv.Perm.mul_apply]

theorem split_nextPin_eq (σ : Equiv.Perm V) (A P : Set V)
    (hA : ∀ x,σ x∉A ↔ x∉A) (hP : Disjoint A P)
    (hh : AllHit (splitHolePerm σ A P hA))
    (j : {x : {z : V // z∉A} // x.val∈P}) :
    (nextPin (splitHolePerm σ A P hA) hh j).val.val =
      (nextPermutation σ P ⟨j.val.val,j.property⟩).val := by
  let e := Equiv.sumCompl (fun x : {z : V // z∉A} => x.val∈P)
  let f : _ → V := fun x => (e x).val
  let π := splitHolePerm σ A P hA
  have hf : ∀ x,f (π x)=σ (f x) := by
    intro x
    simp only [f,π,splitHolePerm,Equiv.permCongr_apply,Equiv.apply_symm_apply,e]
    rfl
  have hinj : Function.Injective f := Subtype.val_injective.comp e.injective
  have hi (k : {x : {z : V // z∉A} // x.val∈P}) : f (Sum.inl k)=k.val.val := rfl
  let i : P := ⟨j.val.val,j.property⟩
  let k : {x : {z : V // z∉A} // x.val∈P} :=
    ⟨⟨(nextPoint σ P i).val,fun h => Set.disjoint_left.mp hP h (nextPoint σ P i).property⟩,
      (nextPoint σ P i).property⟩
  let n := firstPinTime π hh (π (Sum.inl j))+1
  have hnp : (σ^n) i.val=(nextPin π hh j).val.val := by
    rw [show i.val=f (Sum.inl j) from rfl,←semiconj_perm_pow f π σ hf]
    rw [nextPin_spec,hi]
  have hmn : nextTime σ P i≤n := nextTime_min σ P i (Nat.succ_pos _)
    (hnp ▸ (nextPin π hh j).property)
  have hmj : (π^nextTime σ P i) (Sum.inl j)=Sum.inl k := by
    apply hinj
    rw [semiconj_perm_pow f π σ hf,hi,hi]
    exact nextPoint_spec σ P i
  have hnm : n≤nextTime σ P i := nextPin_is_first π hh j (nextTime_pos σ P i) hmj
  have he : n=nextTime σ P i := Nat.le_antisymm hnm hmn
  rw [he,nextPoint_spec] at hnp
  exact hnp.symm

end Heisenberg.Exposure

open scoped Classical
namespace Heisenberg.Conditioning
variable {Ω : Type*} [Fintype Ω]

def mass (μ : Ω → ℝ) (E : Ω → Ω → Prop) (b : Ω) : ℝ :=
  ∑ c,if E b c then μ c else 0

def conditional (μ : Ω → ℝ) (E : Ω → Ω → Prop) (F : Ω → ℝ) (b : Ω) : ℝ :=
  (∑ c,if E b c then μ c * F c else 0)/mass μ E b

lemma mass_nonneg (μ : Ω → ℝ) (hμ : ∀ c,0≤μ c) (E : Ω → Ω → Prop) (b : Ω) :
    0 ≤ mass μ E b := Finset.sum_nonneg (by intro c _; split_ifs; exact hμ c; rfl)

lemma mass_eq (μ : Ω → ℝ) (E : Ω → Ω → Prop) (hE : Equivalence E)
    {a b : Ω} (hab : E a b) : mass μ E a=mass μ E b := by
  apply Finset.sum_congr rfl
  intro c _
  have hh : E a c ↔ E b c := ⟨fun h => hE.trans (hE.symm hab) h,fun h => hE.trans hab h⟩
  simp only [hh]

lemma weight_le_mass (μ : Ω → ℝ) (hμ : ∀ c,0≤μ c) (E : Ω → Ω → Prop)
    (hr : ∀ b,E b b) (b : Ω) : μ b ≤ mass μ E b := by
  simpa only [mass,ite_eq_left (hr b)] using Finset.single_le_sum
    (s:=Finset.univ) (f:=fun c => if E b c then μ c else 0)
    (by intro c _; split_ifs; exact hμ c; rfl) (Finset.mem_univ b)

theorem tower (μ : Ω → ℝ) (hμ : ∀ c,0≤μ c) (E : Ω → Ω → Prop)
    (hE : Equivalence E) (F : Ω → ℝ) :
    (∑ b,μ b*conditional μ E F b)=∑ c,μ c*F c := by
  simp only [conditional,Finset.sum_div,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : μ c=0
  · simp [hc]
  have hm : mass μ E c≠0 := ne_of_gt (lt_of_lt_of_le (lt_of_le_of_ne (hμ c) (Ne.symm hc))
    (weight_le_mass μ hμ E hE.refl c))
  have hs : (∑ b, μ b*((if E b c then μ c*F c else 0)/mass μ E b)) =
      (mass μ E c/mass μ E c)*(μ c*F c) := by
    change _ = (∑ b,if E c b then μ b else 0)/(mass μ E c)*(μ c*F c)
    rw [Finset.sum_div,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : E b c
    · rw [ite_eq_left hb,ite_eq_left (hE.symm hb),mass_eq μ E hE hb]
      ring
    · rw [ite_eq_right hb,ite_eq_right (fun h => hb (hE.symm h))]
      simp
  rw [hs,div_self hm,one_mul]

theorem expected_le (μ : Ω → ℝ) (hμ : ∀ c,0≤μ c) (E : Ω → Ω → Prop)
    (hE : Equivalence E) (F G : Ω → ℝ)
    (h : ∀ b,μ b≠0 → conditional μ E F b≤G b) :
    (∑ c,μ c*F c)≤∑ b,μ b*G b := by
  rw [←tower μ hμ E hE F]
  apply Finset.sum_le_sum
  intro b _
  by_cases hb : μ b=0
  · simp [hb]
  · exact mul_le_mul_of_nonneg_left (h b hb) (hμ b)

end Heisenberg.Conditioning
end

end OAI
