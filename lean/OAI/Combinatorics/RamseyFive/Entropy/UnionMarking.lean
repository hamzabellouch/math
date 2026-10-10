import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.RevealDomains
import OAI.Combinatorics.RamseyFive.Entropy.EntropyCrossEntropy

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {α β ι κ : Type*} [Fintype α] [Fintype β] [Fintype ι] [Fintype κ]
local instance unionMarkingDecEq : DecidableEq ι := Classical.decEq _

def unionRecord (f : α → ι → β) (E₁ E₂ : α → Finset ι) (x : α) (i : ι) : Option β :=
  if i ∈ E₁ x ∪ E₂ x then some (f x i) else none

abbrev RankTypes := (Fin 5 × Fin 5) × Bool × Bool

def unionMask (r : α → ι → RankTypes) (E₁ E₂ : α → Finset ι)
    (x : α) (i : ι) : RankTypes × Bool × Bool :=
  (r x i,decide (i∈E₁ x),decide (i∈E₂ x))

omit [Fintype α] [Fintype β] in
lemma unionRecord_present (f : α → ι → β) (E₁ E₂ : α → Finset ι) (x : α) :
    (∑ i,present (unionRecord f E₁ E₂ x i)) = ((E₁ x ∪ E₂ x).card:ℝ) := by
  have he (i : ι) : present (unionRecord f E₁ E₂ x i) =
      if i∈E₁ x ∪ E₂ x then (1:ℝ) else 0 := by
    simp only [unionRecord]
    split_ifs <;> rfl
  simp_rw [he]
  rw [Finset.sum_ite_mem,Finset.univ_inter]
  simp

theorem union_marking_entropy (p : Law (κ × α))
    (r : α → ι → RankTypes) (f : α → ι → β) (E₁ E₂ : α → Finset ι)
    (S : κ → ι → Finset β) (cap : ℝ) (hcap : 1≤cap)
    (hS : ∀ c i,((S c i).card:ℝ)≤cap)
    (hsupp : ∀ c x,0<p (c,x) → ∀ i,f x i∈S c i) :
    (∑ c,first p c * entropy (pair (fiber p c)
      (unionMask r E₁ E₂) (unionRecord f E₁ E₂))) ≤
      (Fintype.card ι:ℝ)*Real.log 800 +
        (∑ x,second p x*((E₁ x ∪ E₂ x).card:ℝ))*Real.log cap := by
  have hh := conditional_marked_entropy p (unionMask r E₁ E₂)
    (unionRecord f E₁ E₂) S cap hcap hS (by
      intro c x hx i b hb
      dsimp [unionRecord] at hb
      split_ifs at hb with hi
      · cases hb
        exact hsupp c x hx i
      )
  apply hh.trans_eq
  simp only [Fintype.card_fun,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,
    Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat,Real.log_pow,unionRecord_present]
  have hlog : Real.log ((5*5*(2*2))*(2*2):ℝ)+Real.log 2=Real.log 800 := by
    rw [←Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  nlinarith

omit [Fintype α] [Fintype β] [Fintype ι] in
lemma unionRecord_decode_left (f : α → ι → β) (E₁ E₂ : α → Finset ι) (x : α) (i : ι) :
    (if i∈E₁ x then unionRecord f E₁ E₂ x i else none) =
      if i∈E₁ x then some (f x i) else none := by
  by_cases h : i∈E₁ x <;> simp [h,unionRecord]

omit [Fintype α] [Fintype β] [Fintype ι] in
lemma unionRecord_decode_right (f : α → ι → β) (E₁ E₂ : α → Finset ι) (x : α) (i : ι) :
    (if i∈E₂ x then unionRecord f E₁ E₂ x i else none) =
      if i∈E₂ x then some (f x i) else none := by
  by_cases h : i∈E₂ x <;> simp [h,unionRecord]

end

open scoped Classical BigOperators
variable {α κ μ : Type*} [Fintype α] [Fintype κ] [Fintype μ]

def withMessage (p : Law (κ × α)) (M : α → μ) : Law ((κ × μ) × α) :=
  map p (fun z => ((z.1,M z.2),z.2))

lemma first_withMessage (p : Law (κ × α)) (M : α → μ) :
    first (withMessage p M)=mapSnd p M := by
  rw [←map_first,withMessage,map_comp]
  rfl

lemma second_withMessage (p : Law (κ × α)) (M : α → μ) :
    second (withMessage p M)=second p := by
  rw [←map_second,withMessage,map_comp]
  exact map_second p

lemma entropy_withMessage (p : Law (κ × α)) (M : α → μ) :
    entropy (withMessage p M)=entropy p := by
  apply entropy_map_injective
  intro z w h
  have h1 : z.1=w.1 := congrArg (fun u : (κ×μ)×α => u.1.1) h
  have h2 : z.2=w.2 := congrArg (fun u : (κ×μ)×α => u.2) h
  exact Prod.ext h1 h2

lemma mean_withMessage_label (p : Law (κ × α)) (M : α → μ) (g : μ → ℝ) :
    mean (first (withMessage p M)) (fun z => g z.2)=
      mean (second p) (fun x => g (M x)) := by
  rw [first_withMessage,←map_second p,mapSnd,mean_map,mean_map]

lemma withMessage_support (p : Law (κ × α)) (M : α → μ)
    (c : κ) (m : μ) (x : α) (hx : 0<withMessage p M ((c,m),x)) :
    0<p (c,x) ∧ M x=m := by
  obtain ⟨z,hz,he⟩ := map_positive p (fun z => ((z.1,M z.2),z.2)) ((c,m),x) hx
  have hz1 : z.1=c := congrArg (fun u => u.1.1) he
  have hz2 : z.2=x := congrArg Prod.snd he
  have hzm : M z.2=m := congrArg (fun u => u.1.2) he
  have hz' : z=(c,x) := Prod.ext hz1 hz2
  subst z
  exact ⟨hz,hzm⟩

lemma fiber_withMessage_support (p : Law (κ × α)) (M : α → μ)
    (c : κ) (m : μ) (hm : 0<first (withMessage p M) (c,m))
    (x : α) (hx : 0<fiber (withMessage p M) (c,m) x) :
    0<p (c,x) ∧ M x=m := by
  apply withMessage_support
  rw [mass_eq_first_mul_fiber]
  exact mul_pos hm hx

variable {ι β : Type*} [Fintype ι] [Fintype β]

theorem message_deficit_bound (p : Law (κ × (ι → β))) (M : (ι → β) → μ)
    (U : μ → Finset ι) (h : (ι → β) → ℝ) (J L C : ℝ)
    (hcard : ∀ x,((U (M x)).card:ℝ)+h x=Fintype.card ι)
    (hcost : mean (first p) (fun c=>entropy (map (fiber p c) M)) ≤
      C+mean (second p) h*L) :
    mean (first (withMessage p M))
        (fun z=>activeDeficit (fiber (withMessage p M) z) (U z.2) J) ≤
      (Fintype.card ι:ℝ)*J-entropy (second p)+entropy (first p)+C+
        mean (second p) h*(L-J) := by
  have hi : entropy (first (withMessage p M)) ≤
      entropy (first p)+C+mean (second p) h*L := by
    rw [first_withMessage,entropy_chain,first_mapSnd]
    simp only [fiber_mapSnd]
    change entropy (first p)+mean (first p) (fun c=>entropy (map (fiber p c) M)) ≤ _
    linarith
  have hh := entropy_chain (withMessage p M)
  rw [entropy_withMessage] at hh
  have hsecond := entropy_map_le p Prod.snd
  rw [map_second] at hsecond
  have hc : mean (first (withMessage p M)) (fun z=>((U z.2).card:ℝ)) =
      (Fintype.card ι:ℝ)-mean (second p) h := by
    rw [mean_withMessage_label p M (fun m=>((U m).card:ℝ))]
    calc
      _ = mean (second p) (fun x=>(Fintype.card ι:ℝ)-h x) :=
        mean_congr _ (fun x=>by linarith [hcard x])
      _ = _ := by rw [mean_sub,mean_const]
  have he : mean (first (withMessage p M))
        (fun z=>activeDeficit (fiber (withMessage p M) z) (U z.2) J) =
      ((Fintype.card ι:ℝ)-mean (second p) h)*J-
        mean (first (withMessage p M)) (fun z=>entropy (fiber (withMessage p M) z)) := by
    simp only [activeDeficit,mean,mul_sub,Finset.sum_sub_distrib,←mul_assoc,
      ←Finset.sum_mul]
    exact congrArg (fun u=>u*J-∑ z,first (withMessage p M) z *
      entropy (fiber (withMessage p M) z)) hc
  rw [he]
  change entropy p = entropy (first (withMessage p M))+
    mean (first (withMessage p M)) (fun z=>entropy (fiber (withMessage p M) z)) at hh
  nlinarith
end SharpRamseyFive.FiniteEntropy

end

end OAI
