import OAI.Combinatorics.Sidorenko.Types

namespace OAI


section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
namespace FiniteLaw
variable {A I : Type*} [Fintype A] [Fintype I] [DecidableEq I]
noncomputable def diluted (p : FiniteLaw A) (ε : ℝ) (h0 : 0≤ε) (h1 : ε≤1) : FiniteLaw (Option A) where
  weight x := match x with | none => 1-ε | some a => ε*p.weight a
  nonneg x := by cases x with | none => exact sub_nonneg.mpr h1 | some a => exact mul_nonneg h0 (p.nonneg a)
  total := by rw [Fintype.sum_option,←Finset.mul_sum,p.total]; ring
omit [Fintype A] [Fintype I] [DecidableEq I] in
lemma someFunction_injective : Function.Injective (fun a : I → A => fun i => some (a i)) := by
  intro a b h
  funext i; exact Option.some_injective _ (congrFun h i)
omit [Fintype A] [DecidableEq I] in
lemma exists_none_of_not_some (z : I → Option A) (hz : ∀ a : I → A,(fun i => some (a i))≠z) : ∃ i,z i=none := by
  by_contra hn
  push Not at hn
  have hs (i : I) : ∃ a,z i=some a := by
    cases hi : z i with
    | none => exact False.elim (hn i hi)
    | some a => exact ⟨a,rfl⟩
  exact hz (fun i => (hs i).choose) (funext (fun i => (hs i).choose_spec.symm))
lemma diluted_independent_mean (p : FiniteLaw A) (ε : ℝ) (h0 : 0≤ε) (h1 : ε≤1)
    (f : (I → Option A) → ℝ) (hf : ∀ z,(∃ i,z i=none) → f z=0) :
    (independent (fun _ : I => p.diluted ε h0 h1)).mean f=
      ε^Fintype.card I*(independent (fun _ : I => p)).mean (fun a => f (fun i => some (a i))) := by
  unfold mean independent
  rw [Finset.mul_sum]
  symm
  apply Fintype.sum_of_injective (fun a : I → A => fun i => some (a i)) someFunction_injective
  · intro z hz
    rw [hf z (exists_none_of_not_some z (fun a ha => hz ⟨a,ha⟩)),mul_zero]
  · intro a
    simp only [diluted,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
    ring
end FiniteLaw
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators Topology
section Dilution
variable {A B K : Type*} [Fintype A] [Fintype B] [Fintype K] [DecidableEq K]
noncomputable def dilutedPairLaw (p : A → B → FiniteLaw (Activation K)) : Option A → B → FiniteLaw (Activation K)
  | none,_ => inactiveLaw
  | some a,b => p a b
omit [Fintype A] [Fintype B] in
lemma dilutedPairLaw_zero (p : A → B → FiniteLaw (Activation K))
    (hp : ∀ a b α,α≠∅ → (p a b).mean (activationPhi α)=0) :
    ∀ a b α,α≠∅ → (dilutedPairLaw p a b).mean (activationPhi α)=0 := by
  intro a b α hα; cases a with
  | none => exact inactiveLaw_zero α hα
  | some a => exact hp a b α hα
lemma coefficient_dilution_left (π : FiniteLaw A) (ν : FiniteLaw B) (p : A → B → FiniteLaw (Activation K))
    (ε : ℝ) (h0 : 0≤ε) (h1 : ε≤1) :
    averagedCoefficient (π.diluted ε h0 h1) ν (dilutedPairLaw p)=ε^13*averagedCoefficient π ν p := by
  unfold averagedCoefficient typeMapLaw
  rw [FiniteLaw.mean_prod,FiniteLaw.mean_prod]
  have hz (a : Fin 13 → Option A) (ha : ∃ i,a i=none) :
      (FiniteLaw.independent (fun _ : Fin 22 => ν)).mean (fun b => typedCoefficient (dilutedPairLaw p) a b)=0 := by
    obtain ⟨i,hi⟩ := ha
    have he (b : Fin 22 → B) : typedCoefficient (dilutedPairLaw p) a b=0 :=
      typedCoefficient_inactive_left _ a b i (fun j => by rw [hi]; rfl)
    simp only [he,FiniteLaw.mean_const]
  rw [FiniteLaw.diluted_independent_mean π ε h0 h1 _ hz]
  rfl
lemma coefficient_dilution_right (π : FiniteLaw A) (ν : FiniteLaw B) (p : A → B → FiniteLaw (Activation K))
    (ε : ℝ) (h0 : 0≤ε) (h1 : ε≤1) :
    averagedCoefficient ν (π.diluted ε h0 h1) (fun b a => dilutedPairLaw p a b)=
      ε^22*averagedCoefficient ν π (fun b a => p a b) := by
  unfold averagedCoefficient typeMapLaw
  rw [FiniteLaw.mean_prod,FiniteLaw.mean_prod]
  have hd (b : Fin 13 → B) :
      (FiniteLaw.independent (fun _ : Fin 22 => π.diluted ε h0 h1)).mean
        (fun a => typedCoefficient (fun b a => dilutedPairLaw p a b) b a)=
      ε^22*(FiniteLaw.independent (fun _ : Fin 22 => π)).mean
        (fun a => typedCoefficient (fun b a => p a b) b a) := by
    apply FiniteLaw.diluted_independent_mean
    intro a ha
    obtain ⟨j,hj⟩ := ha
    exact typedCoefficient_inactive_right _ b a j (fun i => by rw [hj]; rfl)
  simp only [hd,FiniteLaw.mean_mul]
end Dilution
lemma exists_dilution_gap (t0 t1 : ℝ) (hneg : t0<0) :
    ∃ ε : ℝ,0<ε ∧ ε<1 ∧ (1+ε^13*t0)*(1+ε^22*t1)<1 := by
  let f := fun ε : ℝ => t0+ε^9*t1+ε^22*t0*t1
  have hl : Tendsto f (nhds 0) (nhds t0) := by
    have hc : ContinuousAt f 0 := by dsimp [f]; fun_prop
    simpa only [f,zero_pow (by omega : 9≠0),zero_pow (by omega : 22≠0),zero_mul,add_zero] using hc.tendsto
  have he : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),f ε<0 :=
    (hl.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hneg)
  have hlt : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),ε<1 :=
    nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  have hpos : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),0<ε := self_mem_nhdsWithin
  obtain ⟨ε,hε,hε1,hε0⟩ := (he.and (hlt.and hpos)).exists
  refine ⟨ε,hε0,hε1,?_⟩
  have halg : (1+ε^13*t0)*(1+ε^22*t1)=1+ε^13*f ε := by dsimp [f]; ring
  rw [halg]
  exact add_lt_of_neg_right 1 (mul_neg_of_pos_of_neg (pow_pos hε0 _) hε)
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section PinningRound
variable {I J E C : Type*} [Fintype I] [Fintype J] [Fintype E] [Fintype C]
  [DecidableEq I] [DecidableEq J] [DecidableEq C]
def neighborHistogram (t : E → I) (c : E → C) (i : I) (d : C) : ℕ :=
  ∑ e,if t e=i ∧ c e=d then 1 else 0
lemma histogram_weighted (t : E → I) (c : E → C) (f : I → C → ℝ) :
    (∑ i,∑ d,(neighborHistogram t c i d:ℝ)*f i d)=∑ e,f (t e) (c e) := by
  simp only [neighborHistogram,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,Finset.sum_mul]
  calc
    _ = ∑ i,∑ e,∑ d,(if t e=i ∧ c e=d then (1:ℝ) else 0)*f i d := by
      apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]
    _ = ∑ e,∑ i,∑ d,(if t e=i ∧ c e=d then (1:ℝ) else 0)*f i d := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl; intro e _
      simp [ite_and,ite_mul]

structure VertexPairScores (I J : Type*) where
  left : I → ℝ
  right : J → ℝ
  pair : I → J → ℝ
noncomputable def VertexPairScores.score (s : VertexPairScores I J) (t : E → I) (h : E → J)
    (a : I → I) (b : J → J) : ℝ := ∑ i,s.left (a i)+(∑ j,s.right (b j))+∑ e,s.pair (a (t e)) (b (h e))
noncomputable def roundScores (t : E → I) (h : E → J) (cI : I → C) (cJ : J → C) : VertexPairScores I J where
  left a := -(∑ c,(neighborHistogram t (cJ ∘ h) a c:ℝ)^2)
  right b := -(∑ c,(neighborHistogram h (cI ∘ t) b c:ℝ)^2)
  pair a b := 2*(neighborHistogram t (cJ ∘ h) a (cJ b):ℝ)+2*(neighborHistogram h (cI ∘ t) b (cI a):ℝ)

lemma roundScore_formula (t : E → I) (h : E → J) (cI : I → C) (cJ : J → C)
    (a : I → I) (b : J → J) (ha : ∀ i,cI (a i)=cI i) (hb : ∀ j,cJ (b j)=cJ j) :
    (roundScores t h cI cJ).score t h a b=
    (∑ i,∑ c,(2*(neighborHistogram t (cJ ∘ h) i c:ℝ)*(neighborHistogram t (cJ ∘ h) (a i) c:ℝ)-
      (neighborHistogram t (cJ ∘ h) (a i) c:ℝ)^2))+
    (∑ j,∑ c,(2*(neighborHistogram h (cI ∘ t) j c:ℝ)*(neighborHistogram h (cI ∘ t) (b j) c:ℝ)-
      (neighborHistogram h (cI ∘ t) (b j) c:ℝ)^2)) := by
  have hL := histogram_weighted t (cJ ∘ h) (fun i c => 2*(neighborHistogram t (cJ ∘ h) (a i) c:ℝ))
  have hR := histogram_weighted h (cI ∘ t) (fun j c => 2*(neighborHistogram h (cI ∘ t) (b j) c:ℝ))
  simp only [Function.comp_apply] at hL hR
  simp only [VertexPairScores.score,roundScores,ha,hb,Finset.sum_add_distrib,Finset.sum_neg_distrib]
  rw [←hL,←hR]
  simp only [Finset.sum_sub_distrib]
  have hmul (x y : ℝ) : x*(2*y)=2*x*y := by ring
  simp only [hmul]
  ring

lemma roundScore_loss (t : E → I) (h : E → J) (cI : I → C) (cJ : J → C)
    (a : I → I) (b : J → J) (ha : ∀ i,cI (a i)=cI i) (hb : ∀ j,cJ (b j)=cJ j) :
    (roundScores t h cI cJ).score t h id id-(roundScores t h cI cJ).score t h a b=
    (∑ i,∑ c,((neighborHistogram t (cJ ∘ h) (a i) c:ℝ)-(neighborHistogram t (cJ ∘ h) i c:ℝ))^2)+
    (∑ j,∑ c,((neighborHistogram h (cI ∘ t) (b j) c:ℝ)-(neighborHistogram h (cI ∘ t) j c:ℝ))^2) := by
  rw [roundScore_formula t h cI cJ id id (fun _ => rfl) (fun _ => rfl),roundScore_formula t h cI cJ a b ha hb]
  simp only [id_eq]
  have halg (x y : ℝ) : (2*x*x-x^2)-(2*x*y-y^2)=(y-x)^2 := by ring
  rw [show ∀ x y z w : ℝ,x+y-(z+w)=(x-z)+(y-w) by intros; ring]
  simp only [←Finset.sum_sub_distrib,halg]
end PinningRound
end SidorenkoCounterexample

end

end OAI
