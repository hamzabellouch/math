import OAI.Combinatorics.HadwigerCounterexample.UnaryRecords
import OAI.Combinatorics.HadwigerCounterexample.ConstructionScales

namespace OAI

/-! # Collision Inequality -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Finset Filter
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
variable {I A B : Type} [Fintype I] [Fintype A] [Fintype B]

def density (v w : Wgt I) := fun x => w x/v x
def overlap (v a b : Wgt I) :=
  avg v (fun x => density v a x*density v b x)

theorem overlap_count (P : I→Prop) (p q : Wgt I) (h : ∀ x, 0 ≤ p x) (h' : ∀ x, 0≤ q x) :
    overlap (unifOn P) p q ≤ (Fintype.card I:ℝ) * (∑ i, p i*q i) := by
  classical
  simp only [overlap,density, avg,Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hg := mul_nonneg (h i) (h' i)
  have hw : 0 ≤ (↑(Fintype.card I) : ℝ) := Nat.cast_nonneg _
  by_cases he : P i
  · have hh : 0 < nbr P := by
      have hpos : 0 < Fintype.card {x//P x} := Fintype.card_pos_iff.mpr ⟨⟨i,he⟩⟩
      rw [nbr_eq_card]; exact_mod_cast hpos
    have hd : unifOn P i * (p i/unifOn P i * (q i / unifOn P i))=nbr P*(p i*q i) := by
      rw [unifOn_val,ind_one he]
      field_simp
    rw [hd]
    apply mul_le_mul_of_nonneg_right _ hg
    rw [nbr_eq_card]
    exact_mod_cast Fintype.card_le_of_injective _ (@Subtype.val_injective _ P)
  rw [unifOn_carried P i he,zero_mul]
  exact mul_nonneg hw hg

namespace Volley

/-- law of accepted keys as an unnormalized histogram -/
def hist (v : A → Volley p n I) (t : Tagging p I)
    (μ : Wgt (UnitType p n N)) (rho' : Wgt A) (U : A → UnitType p n N → Prop) :
    Wgt (Keys (p:=p) t N) :=
  fun u => avg rho' (fun a => pr μ (fun x => U a x ∧ (v a).keys t x=u))

set_option maxHeartbeats 800000 in
private theorem record_sum (v w : Volley p n I) {t : Tagging p I} (m : Mixer p n)
    {a b : Pin p n N} {μ δ : Wgt (UnitType p n N)}
    (U V : UnitType p n N → Prop)
    (ha : ∀ x, U x → a.agree x ∧ (∀ i,frameLaw m (onSide x i)))
    (hb : ∀ x, V x → b.agree x ∧ (∀ i,frameLaw m (onSide x i)))
    {ζ : ℝ} {q : ℕ}
    (h : ∀ x,U x → ∀ y,V y → v.keys t x=w.keys t y → v.promised w t m a.sp b.sp x y)
    (hv : v.avoids a.sp q) (hw : w.avoids b.sp q)
    (hz : ζ ≤ 0.004) (hK : ζ*(kslots p I) ≤ 0.004)
    (hμ : SubLaw μ) (hδ : SubLaw δ)
    (hA : a.clear ζ μ) (hB : b.clear ζ δ)
    (hN : 100 ≤ N) (hT : (dim (CheckGram p n) : ℝ) ≤ 0.01*N)
    (L : ℝ)
    (hLf : bp (dim (Ledger (v.frozen a.sp t))) ≤ L)
    (hLg : bp (dim (Ledger (w.frozen b.sp t))) ≤ L) :
    hit N *
      (∑ u : Keys (p:=p) t N, pr μ (fun x => U x ∧ v.keys t x=u) *
        pr δ (fun x => V x ∧ w.keys t x=u)) ≤
      pr (pairW μ δ) (fun x => (rawHoles m).conflict x.1 x.2)+
      2*(hit N*tau N (kslots p I)*L) := by
  classical
  let X := UnitType p n N
  let T := Keys (p:=p) t N
  let K (u : T) (x : X) := U x ∧ v.keys t x=u
  let K' (u : T) (x : X) := V x ∧ w.keys t x=u
  let H := hit N*tau N (kslots p I)*L
  let P := pairW μ δ
  let C (x : X × X) := (rawHoles m).conflict x.1 x.2
  let G (u : T) (x : X × X) := K u x.1 ∧ K' u x.2 ∧ C x
  rw [Finset.mul_sum]
  have hh (i : Keys (p:=p) t N) :
      hit N * (pr μ (K i) * pr δ (K' i))≤ pr P (G i)+H*(pr μ (K i)+pr δ (K' i)) := by
    apply record_hit v w m (K i) (K' i) i _ _ _ hv hw hz hK hμ hδ hA hB hN hT L hLf hLg
    · exact fun x h => ⟨(ha x h.1).1,(ha x h.1).2,h.2⟩
    · exact fun x h => ⟨(hb x h.1).1,(hb x h.1).2,h.2⟩
    exact fun x hx y hy => h x hx.1 y hy.1 (hx.2.trans hy.2.symm)
  refine (Finset.sum_le_sum fun i _ => hh i).trans ?_
  rw [Finset.sum_add_distrib]
  have hi : (∑ i : Keys (p:=p) t N, pr P (G i)) ≤ pr P C := by
    rw [← sum_pr_tag P C (v.keys t ∘ Prod.fst)]
    exact Finset.sum_le_sum fun i _ => pr_mono (subLaw_pair hμ hδ).nz (fun x h => ⟨h.2.2,h.1.2⟩)
  refine add_le_add hi ?_
  have hU : (∑ i : Keys (p:=p) t N, pr μ (K i))≤1 :=
    (sum_pr_tag μ U (v.keys t)).trans_le ((pr_le_tot hμ.nz).trans hμ.total)
  have hV : (∑ i : Keys (p:=p) t N, pr δ (K' i))≤1 :=
    (sum_pr_tag δ V (w.keys t)).trans_le ((pr_le_tot hδ.nz).trans hδ.total)
  have hz : 0 ≤ H := mul_nonneg (mul_nonneg (bp_pos _).le (bp_pos _).le) ((bp_pos _).le.trans hLf)
  rw [← Finset.mul_sum,Finset.sum_add_distrib,mul_comm 2]
  exact mul_le_mul_of_nonneg_left (by linarith only [hU,hV]) hz

set_option maxHeartbeats 1200000 in
theorem collision (v : A→Volley p n I) (w : B→Volley p n I)
    {t : Tagging p I} (m : Mixer p n)
    {a b : Pin p n N} {μ δ : Wgt (UnitType p n N)}
    (rhoA : Wgt A) (rhoB : Wgt B)
    (U : A → UnitType p n N → Prop) (V : B → UnitType p n N → Prop)
    (ha : ∀ i x, U i x → a.agree x ∧ (∀ i,frameLaw m (onSide x i)))
    (hb : ∀ i x, V i x → b.agree x ∧ (∀ i,frameLaw m (onSide x i)))
    {ζ : ℝ} {q K : ℕ}
    (h : ∀ i j x,U i x → ∀ y,V j y → (v i).keys t x=(w j).keys t y →
      (v i).promised (w j) t m a.sp b.sp x y)
    (hv : ∀ i, (v i).avoids a.sp q) (hw : ∀ i, (w i).avoids b.sp q)
    (hκ : planRank a.sp≤K) (hκ' : planRank b.sp≤K)
    (hz : ζ ≤ 0.004) (hK : ζ*(kslots p I) ≤ 0.004) (hslots : kslots p I≤kmax p)
    (hμ : SubLaw μ) (hδ : SubLaw δ) (hu : SubLaw rhoA) (hu' : SubLaw rhoB)
    (hA : a.clear ζ μ) (hB : b.clear ζ δ)
    (hN : 100 ≤ N) (hT : (dim (CheckGram p n) : ℝ) ≤ 0.01*N)
    (hL : (K+(kmax p:ℝ))*num (JointIdx p n) ≤ 0.005*N)
    (J : Keys (p:=p) t N → Prop) :
    overlap (unifOn J) (hist v t μ rhoA U) (hist w t δ rhoB V) ≤
      bp (((kslots p I:ℝ)+0.02)*N)*pr (pairW μ δ) (fun x =>
        (rawHoles m).conflict x.1 x.2) + 2*bp (-0.005*N) := by
  classical
  let k := kslots p I
  let L := bp (0.005*N)
  let C := fun (x : UnitType p n N × _) => (rawHoles m).conflict x.1 x.2
  let X := hist v t μ rhoA U
  let Y := hist w t δ rhoB V
  let H := hit N*tau N k*L
  let D := pr (pairW μ δ) C
  let α (u : Keys (p:=p) t N) i := pr μ (fun x => U i x ∧ (v i).keys t x=u)
  let β (u : Keys (p:=p) t N) i := pr δ (fun x => V i x ∧ (w i).keys t x=u)
  have hX u : 0≤ X u := avg_nonneg hu.nz (fun i => pr_nonneg hμ.nz)
  have hY u : 0≤ Y u := avg_nonneg hu'.nz (fun i => pr_nonneg hδ.nz)
  have hW (f : Plan p n) (hk : planRank f ≤ K) (v : Volley p n I) (hv : v.avoids f q) :
      bp (dim (Ledger (v.frozen f t)))≤L := by
    apply bp_le
    rw [ledger_dim]
    push_cast
    have ht : (planRank (v.frozen f t) : ℝ) ≤ K+(kmax p:ℝ) := by
      have hh := plan_add_rank f (v.keyPlan t)
      rw [key_slots t hv] at hh
      exact_mod_cast (show planRank (f⊔v.keyPlan t) ≤ K+kmax p from
        hh.symm ▸ add_le_add hk hslots)
    exact le_trans (mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg _)) hL
  have hf (x : A × B) :
      hit N * (∑ u : Keys (p:=p) t N, α u x.1*β u x.2) ≤ D+ 2*H :=
    record_sum (v x.1) (w x.2) m (U _) (V _) (ha x.1) (hb x.2) (h x.1 x.2)
      (hv x.1) (hw x.2) hz hK hμ hδ hA hB hN hT L (hW a.sp hκ _ (hv _)) (hW _ hκ' _ (hw _))
  have hh : hit N * (∑ u : Keys (p:=p) t N,X u * Y u) ≤ D + 2*H := by
    let F := pairW rhoA rhoB
    have hh' : 0 ≤ D+2*H := by
      apply add_nonneg (pr_nonneg (subLaw_pair hμ hδ).nz)
      exact mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (bp_pos _).le (bp_pos _).le)
        (bp_pos _).le)
    have hl := (subLaw_pair hu hu').avg_le hh' hf
    rw [avg_mul',avg_sum] at hl
    have ht (u : Keys (p:=p) t N) :
        X u*Y u=avg F (fun x : A×B => α u x.1*β u x.2) := (pairW_separate ..).symm
    simp_rw [ht]; exact hl
  apply (overlap_count J X Y hX hY).trans
  rw [card_space,dim_keys,Nat.cast_mul]
  let Z := bp (((k:ℝ)+0.02)*N)
  have he : Z*hit N = bp ((k:ℝ)*N) := by
    unfold Z hit; rw [← bp_add]; congr 1; ring
  have he' : Z*H = bp (-0.005*N) := by
    unfold H; rw [← mul_assoc,← mul_assoc,he]
    unfold L tau
    rw [← bp_add,← bp_add]; congr 1; ring
  change bp ((k:ℝ)*N)*_≤ Z*D+_
  rw [← he, mul_assoc,← he']
  refine (mul_le_mul_of_nonneg_left hh (bp_pos _).le).trans_eq ?_
  ring
end Volley

theorem collision_scales (p : Shape) (K : ℕ) :
    ∀ᶠ M : ℕ in atTop,∀ᶠ n : ℕ in atTop, let N := M*n;
    100≤N ∧ (dim (CheckGram p n):ℝ) ≤ 0.01*N ∧
      (K+(kmax p:ℝ))*num (JointIdx p n) ≤ 0.005*N := by
  filter_upwards [columns_budget p (δ:=0.01) (by norm_num)
    (16*(ncComp p:ℝ)*p.h) 0 (by positivity) (by norm_num),
    columns_budget p (δ:=0.005) (by norm_num)
    (2*(K+(kmax p:ℝ))) 0 (by positivity) (by norm_num),eventually_ge_atTop 1] with M hM hB hg
  filter_upwards [eventually_ge_atTop 100] with n hn
  specialize hM n (by omega)
  specialize hB n (by omega)
  have hN : 100 ≤ M*n := by nlinarith
  refine ⟨hN,?_,?_⟩
  · rw [checkgram_dim]
    simp only [Nat.cast_mul,Nat.cast_ofNat]; unfold num at hM
    have hi : (↑(Fintype.card (Row p n)):ℝ)≤Fintype.card (Full p n) := by
      have he : Fintype.card (Full p n)=_+_ := Fintype.card_sum ..
      exact_mod_cast (show Fintype.card (Row p n)≤Fintype.card (Full p n) from he.symm ▸
        Nat.le_add_right ..)
    rw [add_zero] at hM
    rw [Nat.cast_mul] at hM
    exact le_trans (mul_le_mul_of_nonneg_left hi (by positivity)) hM
  rw [show num (JointIdx p n) = 2*num (Full p n) from (by
    unfold num JointIdx; rw [Fintype.card_sum]; push_cast; ring)]
  linarith only [hB]

end HadwigerCounterexample

end

end OAI
