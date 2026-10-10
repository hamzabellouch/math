import Mathlib
import OAI.Combinatorics.SharpRamsey.Learning.TestActualRow
import OAI.Combinatorics.SharpRamsey.Learning.PreparedTypical

namespace OAI

section
namespace SharpLogRamsey.RegularPencils
open Finset
open scoped Classical BigOperators
open SharpLogRamsey.Incidence
noncomputable section
variable {A : Type*} [Fintype A]

lemma sum_center_shift (f : A → ℝ) (μ a : ℝ) :
    (∑ x,(f x-a)^2) ≤ 2*∑ x,(f x-μ)^2 +
      2*(Fintype.card A:ℝ)*(μ-a)^2 := by
  calc
    _ ≤ ∑ x, (2*(f x-μ)^2+2*(μ-a)^2) := by
      apply sum_le_sum
      intro x _
      nlinarith [sq_nonneg ((f x-μ)-(μ-a))]
    _ = _ := by rw [sum_add_distrib,←mul_sum]; simp; ring

lemma indicator_sum (C : Finset A) (c : ℝ) :
    (∑ x,if x ∈ C then c else 0) = (C.card:ℝ)*c := by
  rw [←sum_filter]
  simp

lemma indicator_square_sum (C : Finset A) (c : ℝ) :
    (∑ x,(if x ∈ C then c else 0)^2) = (C.card:ℝ)*c^2 := by
  simp_rw [ite_pow,zero_pow (by decide : 2≠0)]
  exact indicator_sum C (c^2)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]

theorem cell_total_variance {n : ℕ} (hdim : Module.finrank K V=n+3)
    (C : Finset (Projectivization K V)) (N : ℝ) (hN : 0<N) :
    (∑ H : Projectivization K (Module.Dual K V),
      (weightedIncidences SharpLogRamsey.Incidence.Incident (fun x => if x∈C then (Nat.card K:ℝ)/N else 0) H -
        (C.card:ℝ)/N)^2) ≤ 4*(Nat.card K:ℝ)^(n+3)*(C.card:ℝ)/N^2 := by
  let q : ℝ := Nat.card K
  let Q : ℝ := ∑ i ∈ range (n+3),q^i
  let u : ℝ := ∑ i ∈ range (n+2),q^i
  let w : Projectivization K V → ℝ := fun x => if x∈C then q/N else 0
  have hq : 1≤q := by
    dsimp [q]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.card_pos (α:=K)).ne')
  have hq0 : 0<q := lt_of_lt_of_le (by norm_num) hq
  have hQ : Q=q*u+1 := by dsimp [Q,u]; rw [geom_sum_succ]
  have hu : 0≤u := by dsimp [u]; positivity
  have hQ0 : 0<Q := by nlinarith
  have hvcard : (Fintype.card (Projectivization K (Module.Dual K V)):ℝ)=Q := by
    rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K _
      (Subspace.dual_finrank_eq.trans hdim)]
    push_cast; rfl
  have hpcard : (Fintype.card (Projectivization K V):ℝ)=Q := by
    rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K _ hdim]
    push_cast; rfl
  have hcQ : (C.card:ℝ)≤Q := by
    rw [←hpcard]
    exact_mod_cast card_le_univ C
  have hc0 : (0:ℝ)≤C.card := Nat.cast_nonneg _
  have hs : ∑ x,w x = (C.card:ℝ)*(q/N) := indicator_sum C (q/N)
  have hs2 : ∑ x,w x^2 = (C.card:ℝ)*(q/N)^2 := indicator_square_sum C (q/N)
  let μ : ℝ := u/Q * ∑ x,w x
  have hshift : μ-(C.card:ℝ)/N = -(C.card:ℝ)/(Q*N) := by
    dsimp [μ]
    rw [hs]
    field_simp
    nlinarith [hQ]
  have hvar := projective_variance_le hdim w
  change (∑ H,(weightedIncidences SharpLogRamsey.Incidence.Incident w H-μ)^2) ≤ q^(n+1)*∑ x,w x^2 at hvar
  rw [hs2] at hvar
  have hshiftbound : Q*(μ-(C.card:ℝ)/N)^2 ≤ (C.card:ℝ)/N^2 := by
    rw [hshift]
    apply (le_of_mul_le_mul_left ?_ (mul_pos hQ0 (sq_pos_of_pos hN)))
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hcQ hc0]
  have hpow : 1≤q^(n+3) := one_le_pow₀ hq
  have hexact : q^(n+1)*((C.card:ℝ)*(q/N)^2) = q^(n+3)*(C.card:ℝ)/N^2 := by
    rw [show n+3=(n+1)+2 by omega,pow_add]; field_simp; ring
  have hmain := sum_center_shift (fun H => weightedIncidences SharpLogRamsey.Incidence.Incident w H) μ ((C.card:ℝ)/N)
  rw [hvcard] at hmain
  change (∑ H,(weightedIncidences SharpLogRamsey.Incidence.Incident w H-(C.card:ℝ)/N)^2) ≤ _
  calc
    _ ≤ 2*(∑ H,(weightedIncidences SharpLogRamsey.Incidence.Incident w H-μ)^2)+2*Q*(μ-(C.card:ℝ)/N)^2 := hmain
    _ ≤ 2*(q^(n+1)*((C.card:ℝ)*(q/N)^2))+2*((C.card:ℝ)/N^2) := by nlinarith
    _ ≤ 4*q^(n+3)*(C.card:ℝ)/N^2 := by
      rw [hexact]
      have hh := mul_le_mul_of_nonneg_right hpow (show 0≤(C.card:ℝ)/N^2 by positivity)
      have hh' : (C.card:ℝ)/N^2 ≤ q^(n+3)*(C.card:ℝ)/N^2 := by
        simpa only [one_mul,mul_div_assoc] using hh
      calc
        _ ≤ 2*(q^(n+3)*(C.card:ℝ)/N^2)+
            2*(q^(n+3)*(C.card:ℝ)/N^2) := by gcongr
        _ = _ := by ring

end
end SharpLogRamsey.RegularPencils

namespace SharpLogRamsey.RegularPencils
open Finset
open scoped Classical BigOperators
noncomputable section
variable {A ι : Type*} [Fintype A] [Fintype ι]

def exceptional (l : A → ℝ) (c : ι → A → ℝ) (f : ι → ℝ) : Finset A :=
  univ.filter (fun H =>  1/10  <  |l H-1| ∨ ∃ i,1/50  <  |c i H-f i|)

lemma exceptional_indicator (l : A → ℝ) (c : ι → A → ℝ) (f : ι → ℝ) (H : A) :
    (if H∈exceptional l c f then (1:ℝ) else 0)  ≤
      100*(l H-1)^2+2500*∑ i,(c i H-f i)^2 := by
  split_ifs with he
  · rcases (mem_filter.mp he).2 with hl | ⟨i,hi⟩
    · have hs : (1/10:ℝ)^2  <  (l H-1)^2 := by nlinarith [sq_abs (l H-1)]
      have hp : 0  ≤  ∑ i,(c i H-f i)^2 := sum_nonneg (fun _ _ =>  sq_nonneg _)
      nlinarith
    · have hs : (1/50:ℝ)^2  <  (c i H-f i)^2 := by nlinarith [sq_abs (c i H-f i)]
      have hi' := single_le_sum (f:=fun i =>  (c i H-f i)^2)
        (fun _ _ =>  sq_nonneg _) (mem_univ i)
      nlinarith [sq_nonneg (l H-1)]
  · positivity

theorem exceptional_card (l : A → ℝ) (c : ι → A → ℝ) (f : ι → ℝ)
    (V W : ℝ) (hl : ∑ H,(l H-1)^2  ≤  V)
    (hc : ∑ i,∑ H,(c i H-f i)^2  ≤  W) :
    ((exceptional l c f).card:ℝ)  ≤  100*V+2500*W := by
  have hh := sum_le_sum (s:=univ) (fun H _ =>  exceptional_indicator l c f H)
  simp only [sum_add_distrib,←mul_sum] at hh
  rw [sum_comm] at hh
  have hi : (∑ H,if H∈exceptional l c f then (1:ℝ) else 0) =
      ((exceptional l c f).card:ℝ) := by rw [←sum_filter]; simp
  rw [hi] at hh
  linarith

theorem exceptional_mass (l : A → ℝ) (c : ι → A → ℝ) (f : ι → ℝ)
    (V W : ℝ) (hl : ∑ H,(l H-1)^2  ≤  V)
    (hc : ∑ i,∑ H,(c i H-f i)^2  ≤  W) :
    (∑ H∈exceptional l c f,l H)  ≤  201*V+5000*W := by
  have hcard := exceptional_card l c f V W hl hc
  calc
    _  ≤  ∑ H∈exceptional l c f,(2+(l H-1)^2) := by
      apply sum_le_sum
      intro H _
      nlinarith [sq_nonneg (l H-3/2)]
    _ = 2*((exceptional l c f).card:ℝ)+∑ H∈exceptional l c f,(l H-1)^2 := by
      rw [sum_add_distrib]; simp; ring
    _  ≤  2*((exceptional l c f).card:ℝ)+V := by
      gcongr
      exact (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ =>  sq_nonneg _)).trans hl
    _  ≤  _ := by linarith

lemma clip_nonneg (x : ℝ) : 0  ≤  min 1 (x^2) := le_min (by norm_num) (sq_nonneg _)
lemma clip_le_one (x : ℝ) : min 1 (x^2)  ≤  1 := min_le_left _ _
lemma clip_sum (x : A → ℝ) : (∑ H,min 1 ((x H)^2))  ≤  ∑ H,(x H)^2 :=
  sum_le_sum (fun _ _ =>  min_le_right _ _)

end
end SharpLogRamsey.RegularPencils

namespace SharpLogRamsey.PreparedVariance
open Finset PreparedRow PreparedTypical Incidence RegularPencils
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V I : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype I]
local instance flat_JoinedPreparedVariance_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedPreparedVariance_2 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedPreparedVariance_3 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

lemma mass_weighted (C : Finset (Projectivization K V)) (c : ℝ≥0)
    (H : Projectivization K (Module.Dual K V)) :
    mass C c H=weightedIncidences SharpLogRamsey.Incidence.Incident (fun x => if x∈C then (c:ℝ) else 0) H := by
  dsimp [mass,weightedIncidences]
  have he : (∑ x : Projectivization K V,if SharpLogRamsey.Incidence.Incident x H then (if x∈C then (c:ℝ) else 0) else 0)=
      ∑ x∈C.filter (fun y => y.submodule≤LinearMap.ker H.rep),(c:ℝ) := by
    rw [sum_filter]
    calc
      _ = ∑ x,if x∈C then (if x.submodule≤LinearMap.ker H.rep then (c:ℝ) else 0) else 0 := by
        apply sum_congr rfl
        intro x _
        simp only [incident_iff_submodule]
        split_ifs <;> rfl
      _ = _ := by rw [←sum_filter]; simp
  rw [he]
  simp [mul_comm]

lemma actual_cell_variance {n : ℕ} (hdim : Module.finrank K V=n+3)
    (C : Finset (Projectivization K V)) (N : ℝ) (hN : 0<N)
    (c : ℝ≥0) (hc : (c:ℝ)=(Nat.card K:ℝ)/N) :
    (∑ H : Projectivization K (Module.Dual K V),(mass C c H-(C.card:ℝ)/N)^2)≤
      4*(Nat.card K:ℝ)^(n+3)*(C.card:ℝ)/N^2 := by
  have hh := cell_total_variance hdim C N hN
  simpa only [mass_weighted,hc] using hh

theorem actual_exceptions {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S : Finset (Projectivization K V)) (hS : S.Nonempty)
    (C : I→Finset (Projectivization K V)) (hC : (∑ i,(C i).card)≤S.card)
    (c : ℝ≥0) (hc : (c:ℝ)=(Nat.card K:ℝ)/(S.card:ℝ)) :
    let E := exceptional (mass S c) (fun i => mass (C i) c)
      (fun i => ((C i).card:ℝ)/(S.card:ℝ))
    let Q := (Nat.card K:ℝ)^(n+3)/(S.card:ℝ)
    (∑ H : Projectivization K (Module.Dual K V),(mass S c H-1)^2)≤4*Q ∧
    (∑ i,∑ H : Projectivization K (Module.Dual K V),
      (mass (C i) c H-((C i).card:ℝ)/(S.card:ℝ))^2)≤4*Q ∧
    (E.card:ℝ)≤10400*Q ∧ (∑ H∈E,mass S c H)≤20804*Q := by
  dsimp only
  have hN : (0:ℝ)<S.card := by exact_mod_cast card_pos.mpr hS
  have hs := actual_cell_variance hdim S S.card hN c hc
  have hi (i : I) := actual_cell_variance hdim (C i) S.card hN c hc
  rw [div_self hN.ne'] at hs
  have hr : 4*(Nat.card K:ℝ)^(n+3)*(S.card:ℝ)/(S.card:ℝ)^2=
      4*((Nat.card K:ℝ)^(n+3)/(S.card:ℝ)) := by field_simp
  rw [hr] at hs
  have htotal : (∑ i,∑ H : Projectivization K (Module.Dual K V),
      (mass (C i) c H-((C i).card:ℝ)/(S.card:ℝ))^2)≤
        4*((Nat.card K:ℝ)^(n+3)/(S.card:ℝ)) := by
    calc
      _ ≤ ∑ i,4*(Nat.card K:ℝ)^(n+3)*((C i).card:ℝ)/(S.card:ℝ)^2 :=
        sum_le_sum (fun i _ => hi i)
      _ = (4*(Nat.card K:ℝ)^(n+3)/(S.card:ℝ)^2)*(∑ i,((C i).card:ℝ)) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro i _
        ring
      _ ≤ (4*(Nat.card K:ℝ)^(n+3)/(S.card:ℝ)^2)*(S.card:ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact_mod_cast hC
      _ = _ := by field_simp
  refine ⟨hs,htotal,?_,?_⟩
  · have h := exceptional_card (mass S c) (fun i => mass (C i) c)
      (fun i => ((C i).card:ℝ)/(S.card:ℝ)) _ _ hs htotal
    linarith
  · have h := exceptional_mass (mass S c) (fun i => mass (C i) c)
      (fun i => ((C i).card:ℝ)/(S.card:ℝ)) _ _ hs htotal
    linarith

def weights (S : Finset (Projectivization K V)) (C : I→Finset (Projectivization K V))
    (c : ℝ≥0) : Option (Option I)→Projectivization K (Module.Dual K V)→ℝ
  | none,H => min 1 ((mass S c H-1)^2)
  | some none,H => if H∈exceptional (mass S c) (fun i => mass (C i) c)
      (fun i => ((C i).card:ℝ)/(S.card:ℝ)) then 1 else 0
  | some (some i),H => min 1 ((mass (C i) c H-((C i).card:ℝ)/(S.card:ℝ))^2)

lemma weights_nonneg (S : Finset (Projectivization K V)) (C : I→Finset (Projectivization K V))
    (c : ℝ≥0) (i : Option (Option I)) (H : Projectivization K (Module.Dual K V)) :
    0≤weights S C c i H := by
  cases i with
  | none => exact clip_nonneg _
  | some i => cases i with
    | none => dsimp [weights]; split_ifs <;> norm_num
    | some i => exact clip_nonneg _

lemma weights_le_one (S : Finset (Projectivization K V)) (C : I→Finset (Projectivization K V))
    (c : ℝ≥0) (i : Option (Option I)) (H : Projectivization K (Module.Dual K V)) :
    weights S C c i H≤1 := by
  cases i with
  | none => exact clip_le_one _
  | some i => cases i with
    | none => dsimp [weights]; split_ifs <;> norm_num
    | some i => exact clip_le_one _

lemma weights_total {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S : Finset (Projectivization K V)) (hS : S.Nonempty)
    (C : I→Finset (Projectivization K V)) (hC : (∑ i,(C i).card)≤S.card)
    (c : ℝ≥0) (hc : (c:ℝ)=(Nat.card K:ℝ)/(S.card:ℝ)) :
    (∑ i,∑ H,weights S C c i H)≤10408*((Nat.card K:ℝ)^(n+3)/(S.card:ℝ)) := by
  have hh := actual_exceptions hdim S hS C hC c hc
  dsimp only at hh
  have hs := clip_sum (fun H => mass S c H-1)
  have hi := sum_le_sum (s:=univ) (fun i _ => clip_sum (fun H => mass (C i) c H-((C i).card:ℝ)/(S.card:ℝ)))
  simp only [Fintype.sum_option,weights]
  have he : (∑ H,if H∈exceptional (mass S c) (fun i => mass (C i) c)
      (fun i => ((C i).card:ℝ)/(S.card:ℝ)) then (1:ℝ) else 0)=
      ((exceptional (mass S c) (fun i => mass (C i) c)
      (fun i => ((C i).card:ℝ)/(S.card:ℝ))).card:ℝ) := by rw [←sum_filter]; simp
  rw [he]
  linarith [hh.1,hh.2.1,hh.2.2.1]

theorem exists_regular {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S : Finset (Projectivization K V)) (hS : S.Nonempty)
    (C : I→Finset (Projectivization K V)) (hC : (∑ i,(C i).card)≤S.card)
    (c : ℝ≥0) (hc : (c:ℝ)=(Nat.card K:ℝ)/(S.card:ℝ))
    (T : ℝ) (hT : 0≤T)
    (hmean : (∑ k∈range (n+2),(Nat.card K:ℝ)^k)/(∑ k∈range (n+3),(Nat.card K:ℝ)^k)*
      (10408*((Nat.card K:ℝ)^(n+3)/(S.card:ℝ)))≤T/2) :
    ∃ D : Finset (Projectivization K V),
      (D.card:ℝ)*(T/2)^2≤10408*(Nat.card K:ℝ)^(2*n+4)/(S.card:ℝ) ∧
      ∀ x∉D,∀ i,(∑ H∈pencil x,weights S C c i H)<T := by
  let D := univ.biUnion (fun i => univ.filter (fun x : Projectivization K V =>
    T≤∑ H,if SharpLogRamsey.Incidence.Incident x H then weights S C c i H else 0))
  have hp : (0:ℝ)≤(∑ k∈range (n+2),(Nat.card K:ℝ)^k)/(∑ k∈range (n+3),(Nat.card K:ℝ)^k) := by positivity
  have hmass := weights_total hdim S hS C hC c hc
  have hm (i : Option (Option I)) :
      (∑ k∈range (n+2),(Nat.card K:ℝ)^k)/(∑ k∈range (n+3),(Nat.card K:ℝ)^k)*∑ H,weights S C c i H≤T/2 := by
    apply le_trans _ hmean
    apply mul_le_mul_of_nonneg_left _ hp
    apply le_trans _ hmass
    exact single_le_sum (fun j _ => sum_nonneg (fun H _ => weights_nonneg S C c j H)) (mem_univ i)
  have hd := pencil_family_tail hdim (weights S C c) (weights_nonneg S C c) (weights_le_one S C c) T hT hm
  refine ⟨D,?_,?_⟩
  · apply hd.trans
    calc
      _ ≤ (Nat.card K:ℝ)^(n+1)*(10408*((Nat.card K:ℝ)^(n+3)/(S.card:ℝ))) :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = _ := by rw [show 2*n+4=(n+1)+(n+3) by omega,pow_add]; ring
  · intro x hx i
    have hn : ¬T≤∑ H,if SharpLogRamsey.Incidence.Incident x H then weights S C c i H else 0 := by
      intro he
      exact hx (mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨mem_univ _,he⟩⟩)
    have he : (∑ H∈pencil x,weights S C c i H)=
        ∑ H,if SharpLogRamsey.Incidence.Incident x H then weights S C c i H else 0 := by
      rw [pencil,sum_filter]
      apply sum_congr rfl
      intro H _
      simp only [incident_iff_submodule]
    rw [he]
    exact lt_of_not_ge hn

end
end SharpLogRamsey.PreparedVariance

end

end OAI
