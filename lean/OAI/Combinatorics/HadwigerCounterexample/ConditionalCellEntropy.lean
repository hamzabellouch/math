import OAI.Combinatorics.HadwigerCounterexample.GradientRealization
import OAI.Combinatorics.HadwigerCounterexample.WalshBounds

namespace OAI

/-! # Conditional Cell Entropy -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Module Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

theorem plan_add_disjoint (a b : Plan p n) (h : ∀ z, Disjoint (a z) (b z)) :
    planRank (a⊔b)=planRank a+planRank b := by
  unfold planRank
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have he := Submodule.finrank_sup_add_finrank_inf_eq (a i) (b i)
  rw [(h i).eq_bot,finrank_bot,add_zero] at he
  exact he

theorem plan_new_disjoint (a b : Plan p n) (h : ∀ z,Disjoint (a z) (b z)) :
    planNew a b=planRank b := by rw [planNew,plan_add_disjoint a b h,Nat.add_sub_cancel_left]

variable {I : Type} [Fintype I]

def kslots (p : Shape) (I : Type) [Fintype I] :=
  Fintype.card I*(p.g-1)*2
def kmax (p : Shape) := 56*(p.g-1)
theorem slots_budget {w : I→Bool} (v : Volley p n I)
    (hb : v.bounded w) : kslots p I ≤ kmax p := by
  classical
  have h := v.call_count hb
  unfold kslots kmax; nlinarith

instance instFKeys (t : Tagging p I) (N : ℕ) : Fintype (Keys (p:=p) t N) :=
  by classical exact inferInstance

theorem dim_keys (t : Tagging p I) :
    dim (Keys (p:=p) t N) = kslots p I * N := by
  have h (l : Tag p.g) :
      dim (AtomKey (p:=p) l N)=(p.g-1)*(2*N) := by
    unfold AtomKey dim

    rw [finrank_pi_fintype]
    have he : finrank F (Bool → Vec (Fin N))=2*N := by
      rw [finrank_pi_fintype]
      simp_rw [show finrank F (Vec (Fin N))=_ from dim_vec _]
      simp
    simp_rw [he]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_star]; rfl
  unfold dim Keys kslots
  rw [finrank_pi_fintype]
  have hx i : finrank F (AtomKey (p:=p) (t i) N)=(p.g-1)*(2*N) := h (t i)
  simp_rw [hx]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id]
  ring

namespace Volley
variable {v : Volley p n I}

theorem key_slots (t : Tagging p I) {q} {a : Plan p n}
    (h : v.avoids a q) :
    planNew a (v.keyPlan t) = kslots p I := by
  classical
  let Y := visits p t
  have hh i := key_independent v t h i
  have he (z : Place p) : dim (keyPlan v t z)=Fintype.card (Y z.1) :=
    mrk_inj.mp (hh z).1
  rw [plan_new_disjoint a _ (fun i => Disjoint.mono_left (pin_le_table a i)
    (hh i).2.symm), planRank,Fintype.sum_prod_type]
  simp_rw [Fintype.sum_bool,he,←two_mul,←Finset.mul_sum]
  have hE : ∑ i : Comp p.g,Fintype.card (Y i)=Fintype.card I*(p.g-1) := by
    have hf {A : Type} [Fintype A] (p : A → Prop) [DecidablePred p] :
        Fintype.card {i:A//p i}=∑ i:A, if p i then (1:ℕ) else 0 := by
      rw [Fintype.card_subtype,←Finset.sum_filter]; simp

    have hY (i) : Fintype.card (Y i)=∑ j:I,if inc i (t j) then (1:ℕ) else 0 := hf _
    simp_rw [hY]
    rw [Finset.sum_comm]
    simp_rw [← hf (fun i => inc i _)]
    have hz (j) : Fintype.card {i:Comp p.g//inc i (t j)}=p.g-1 := card_star (t j)
    simp_rw [hz]
    simp
  rw [hE]; unfold kslots; ring

/-- chosen reference x fixes the pin made of a and all key directions
for every y in the same pin which agrees on query key. -/
theorem key_pin (t : Tagging p I) {a : Pin p n N} {x y : UnitType p n N}
    (hx : a.agree x) (hy : a.agree y) (h : v.keys t x=v.keys t y) :
    (Pin.make (v.frozen a.sp t) x).agree y := by
  classical
  intro i u hu
  obtain ⟨l,hl,r,⟨z,rfl⟩,rfl⟩ := Submodule.mem_sup.mp
    (show u∈a.sp i⊔v.keyPlan t i from hu)
  have hZ : images y i * v.keyM t i.1 = images x i * v.keyM t i.1 := by
    ext b j
    obtain ⟨k,hk⟩ := j
    have ht := congr_fun (congr_fun (congr_fun h k) (⟨i.1,hk⟩ : TagStar _)) i.2
    rw [v.keys_loc,v.keys_loc] at ht
    exact congr_fun ht.symm b
  change images y i *ᵥ _ = images x i *ᵥ _
  rw [Matrix.mulVec_add,Matrix.mulVec_add,hx _ _ hl,hy _ _ hl]
  rw [mulVecLin_apply,mulVec_mulVec,mulVec_mulVec,hZ]
end Volley

def tau (N k : ℕ) := bp (-((k:ℝ)+0.01)*N)
def hit (N : ℕ) := bp (-0.02*N)

theorem in_clear {a f : Pin p n N} {k : ℕ} {ζ : ℝ} {w : Wgt (UnitType p n N)}
    (hz : ζ ≤ 0.004) (hkz : ζ*k ≤ 0.004)
    (hw : SubLaw w) (h : a.clear ζ w) (hF : a.sp≤f.sp) (hk : planRank f.sp=planRank a.sp+k)
    (S : UnitType p n N → Prop)
    (hS : ∀ x,S x → f.agree x) (ht : tau N k ≤ pr w S) :
    IsLaw (onW w S) ∧ f.clear 0.05 (onW w S) := by
  classical
  have hpos : 0 < pr w S := lt_of_lt_of_le (bp_pos _) ht
  have hh : IsLaw (onW w S) := normW_law (subW_nonneg hw.nz _) hpos
  refine ⟨hh,fun b => ?_⟩
  let t := planNew f.sp b.sp
  by_cases he : t=0
  · change pr _ _ ≤ fee N _ t
    rw [he,fee]
    simp only [Nat.cast_zero,mul_zero,zero_mul,bp_zero]
    exact (pr_le_tot hh.nz).trans hh.total.le
  let R := fun x => S x ∧ b.agree x
  by_cases hf : 0 < pr w R
  · obtain ⟨x,⟨hx,hB⟩,_⟩ := exists_of_pr_pos hw.nz hf
    let c := Pin.make (f.sp⊔b.sp) x
    have hc : pr w R≤ fee N ζ (planNew a.sp c.sp) := (pr_mono hw.nz (q:=c.agree)
      (fun y hy => ((Pin.combine (hS x hx) hB).mpr ⟨hS _ hy.1,hy.2⟩))).trans (h c)
    have hN : planNew a.sp c.sp=k+t := by
      have hh : planNew a.sp f.sp+t=planNew a.sp c.sp := planNew_mono_add hF
      rw [← hh]
      rw [planNew, sup_eq_right.mpr hF,hk, Nat.add_sub_cancel_left]
    rw [hN] at hc
    rw [pr_on]
    refine ((div_le_div₀ (bp_pos _).le hc (bp_pos _) ht)).trans ?_
    unfold fee
    rw [←bp_sub]
    refine bp_le ?_
    have h1 : 1 ≤ (t:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr he
    have hg := mul_le_mul_of_nonneg_right hz (show 0≤(t:ℝ) from Nat.cast_nonneg _)
    rw [Nat.cast_add]
    change _ ≤ -(1-0.05)*(t : ℝ)*N
    rw [← sub_mul]
    exact mul_le_mul_of_nonneg_right (by linarith only [hkz,h1,hg]) (Nat.cast_nonneg _)
  · rw [pr_on]
    exact (div_nonpos_of_nonpos_of_nonneg (not_lt.mp hf) hpos.le).trans (bp_pos _).le

end HadwigerCounterexample

end

end OAI
