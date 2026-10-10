import Mathlib
import OAI.Combinatorics.SharpRamsey.Parameters.EndpointScales

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {A B : Type*} [Fintype A] [Fintype B]

lemma Law.support_card_pos (p : Law A) (S : Finset A)
    (hs : ∀ a,a∉S→p.mass a=0) : 0<S.card := by
  by_contra h
  have he : S=∅ := card_eq_zero.mp (by omega)
  have hz : ∑ a,p.mass a=0 := sum_eq_zero (fun a _=>hs a (by simp [he]))
  linarith [p.total]

lemma entropy_snd_fiber_lower (p : Law (A×B)) (S : Finset (A×B))
    (hs : ∀ z,z∉S→p.mass z=0) (T : ℝ) (hT : 0<T)
    (hcard : ∀ b,((univ.filter (fun a=>(a,b)∈S)).card:ℝ)≤T) :
    entropy p-log T≤entropy p.snd := by
  have he : ∑ b,p.snd.mass b*entropy (p.condFst b)≤log T := by
    calc
      _ ≤ ∑ b,p.snd.mass b*log T := by
        apply sum_le_sum
        intro b _
        by_cases hb : p.snd.mass b=0
        · simp [hb]
        have hsup : ∀ a,a∉univ.filter (fun a=>(a,b)∈S)→(p.condFst b).mass a=0 := by
          intro a ha
          rw [Law.condFst_mass _ _ hb,hs (a,b) (by simpa using ha),zero_div]
        have hp : (0:ℝ)<(univ.filter (fun a=>(a,b)∈S)).card := by
          exact_mod_cast (p.condFst b).support_card_pos _ hsup
        exact mul_le_mul_of_nonneg_left
          ((entropy_le_log_card (p.condFst b) _ hsup).trans ((log_le_log_iff hp hT).2 (hcard b)))
          (p.snd.nonneg b)
      _ = log T := by rw [←sum_mul,p.snd.total,one_mul]
  linarith [entropy_chain p]

lemma entropy_fst_fiber_lower (p : Law (A×B)) (S : Finset (A×B))
    (hs : ∀ z,z∉S→p.mass z=0) (T : ℝ) (hT : 0<T)
    (hcard : ∀ a,((univ.filter (fun b=>(a,b)∈S)).card:ℝ)≤T) :
    entropy p-log T≤entropy p.fst := by
  have hh:=entropy_snd_fiber_lower p.swap (S.image Prod.swap) (by
    rintro ⟨b,a⟩ hz
    exact hs (a,b) (fun ha=>hz (mem_image.mpr ⟨(a,b),ha,rfl⟩))) T hT (by
      intro a
      have he : univ.filter (fun b=>(b,a)∈S.image Prod.swap)=univ.filter (fun b=>(a,b)∈S) := by
        ext b
        simp only [mem_filter,mem_univ,true_and]
        constructor
        · intro hb
          obtain ⟨⟨x,y⟩,hh,heq⟩:=mem_image.mp hb
          have hx : x=a := congrArg Prod.snd heq
          have hy : y=b := congrArg Prod.fst heq
          simpa only [hx,hy] using hh
        · intro hb; exact mem_image.mpr ⟨(a,b),hb,rfl⟩
      rw [he]
      exact hcard a)
  simpa only [entropy_swap,Law.swap_snd] using hh

def highGoodFirst (p : Law (A×B)) (M L κ U : ℝ) (a : A) : Prop :=
  goodFirst p M L κ (1/50) a ∧ p.fst.mass a≤U

def highGoodSecond (p : Law (A×B)) (M L κ U : ℝ) (b : B) : Prop :=
  goodSecond p M L κ (1/50) b ∧ p.snd.mass b≤U

lemma Law.event_not_and (p : Law A) (P Q : A→Prop) :
    p.event (univ.filter (fun a=>¬(P a∧Q a)))≤
      p.event (univ.filter (fun a=>¬P a))+p.event (univ.filter (fun a=>¬Q a)) := by
  simp only [Law.event,sum_filter,←sum_add_distrib]
  apply sum_le_sum
  intro a _
  by_cases hp : P a <;> by_cases hq : Q a <;> simp [hp,hq,p.nonneg]

theorem high_second_upper_mass (p : Law (A×B)) (S : Finset (A×B))
    (DB : Finset B) (hs : ∀ z,z∉S→p.mass z=0)
    (hb : ∀ b,b∉DB→p.snd.mass b=0) (T L₀ κ : ℝ) (hT : 0<T) (hκ : 0<κ)
    (hcard : ∀ b,((univ.filter (fun a=>(a,b)∈S)).card:ℝ)≤T) :
    p.snd.event (univ.filter (fun b=>exp (κ-L₀)<p.snd.mass b))≤
      (L₀+log T-entropy p+DB.card*exp (-L₀))/κ := by
  exact (p.snd.heavy_atoms DB hb L₀ hκ).trans
    (div_le_div_of_nonneg_right (by linarith [entropy_snd_fiber_lower p S hs T hT hcard]) hκ.le)

theorem high_first_upper_mass (p : Law (A×B)) (S : Finset (A×B))
    (DA : Finset A) (hs : ∀ z,z∉S→p.mass z=0)
    (ha : ∀ a,a∉DA→p.fst.mass a=0) (T L₀ κ : ℝ) (hT : 0<T) (hκ : 0<κ)
    (hcard : ∀ a,((univ.filter (fun b=>(a,b)∈S)).card:ℝ)≤T) :
    p.fst.event (univ.filter (fun a=>exp (κ-L₀)<p.fst.mass a))≤
      (L₀+log T-entropy p+DA.card*exp (-L₀))/κ := by
  exact (p.fst.heavy_atoms DA ha L₀ hκ).trans
    (div_le_div_of_nonneg_right (by linarith [entropy_fst_fiber_lower p S hs T hT hcard]) hκ.le)

theorem high_second_bad (p : Law (A×B)) (S : Finset (A×B)) (DB : Finset B)
    (hs : ∀ z,z∉S→p.mass z=0) (hb : ∀ b,b∉DB→p.snd.mass b=0)
    (M L L₀ κ T : ℝ) (hM : 0<M) (hκ : 0<κ) (hT : 0<T)
    (hB : (DB.card:ℝ)≤M)
    (hcard : ∀ b,((univ.filter (fun a=>(a,b)∈S)).card:ℝ)≤T) :
    p.snd.event (univ.filter (fun b=>¬highGoodSecond p M L κ (exp (κ-L₀)) b))≤
      exp (-κ)+(L-entropy p+S.card*exp (-L))/(κ*(1/50))+
        (L₀+log T-entropy p+DB.card*exp (-L₀))/κ := by
  unfold highGoodSecond
  convert (p.snd.event_not_and (goodSecond p M L κ (1/50)) (fun b=>p.snd.mass b≤exp (κ-L₀))).trans (add_le_add
    (badSecond_mass p S hs DB hb M L κ (1/50) hM hB hκ (by norm_num))
    (by simpa only [not_le] using high_second_upper_mass p S DB hs hb T L₀ κ hT hκ hcard)) using 1
  congr 1
  exact filter_congr_decidable _ _ _

theorem high_first_bad (p : Law (A×B)) (S : Finset (A×B)) (DA : Finset A)
    (hs : ∀ z,z∉S→p.mass z=0) (ha : ∀ a,a∉DA→p.fst.mass a=0)
    (M L L₀ κ T : ℝ) (hM : 0<M) (hκ : 0<κ) (hT : 0<T)
    (hA : (DA.card:ℝ)≤M)
    (hcard : ∀ a,((univ.filter (fun b=>(a,b)∈S)).card:ℝ)≤T) :
    p.fst.event (univ.filter (fun a=>¬highGoodFirst p M L κ (exp (κ-L₀)) a))≤
      exp (-κ)+(L-entropy p+S.card*exp (-L))/(κ*(1/50))+
        (L₀+log T-entropy p+DA.card*exp (-L₀))/κ := by
  unfold highGoodFirst
  convert (p.fst.event_not_and (goodFirst p M L κ (1/50)) (fun a=>p.fst.mass a≤exp (κ-L₀))).trans (add_le_add
    (badFirst_mass p S hs DA ha M L κ (1/50) hM hA hκ (by norm_num))
    (by simpa only [not_le] using high_first_upper_mass p S DA hs ha T L₀ κ hT hκ hcard)) using 1
  congr 1
  exact filter_congr_decidable _ _ _
end
end SharpLogRamsey.Selection

end

end OAI
