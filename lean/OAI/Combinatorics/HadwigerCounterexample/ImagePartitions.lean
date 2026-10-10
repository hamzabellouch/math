import OAI.Combinatorics.HadwigerCounterexample.RawFrameLaws

namespace OAI

/-! # Image Partitions -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

theorem plan_mono {a b : Plan p n} (h : a ≤ b) : planRank a ≤ planRank b :=
  Finset.sum_le_sum fun i _ => Submodule.finrank_mono (h i)

/-- Joint nominal rank modulo pins. -/
def planNew (a b : Plan p n) := planRank (a⊔b) - planRank a

theorem plan_add_rank (a b : Plan p n) :
    planRank a + planNew a b = planRank (a⊔b) :=
  Nat.add_sub_of_le (plan_mono le_sup_left)

theorem planNew_mono_add {a b c : Plan p n} (h : a ≤ b) :
    planNew a b + planNew b c = planNew a (b⊔c) := by
  have he := plan_add_rank a b
  have hf := plan_add_rank b c
  have hg := plan_add_rank a (b⊔c)
  rw [sup_eq_right.mpr h] at he
  rw [sup_eq_right.mpr (le_trans h le_sup_left)] at hg
  omega

def Pin.make (a : Plan p n) (x : UnitType p n N) : Pin p n N := ⟨a,images x⟩

theorem Pin.combine {a b : Pin p n N} {x y} (ha : a.agree x) (hb : b.agree x) :
    (Pin.make (a.sp ⊔ b.sp) x).agree y ↔ a.agree y ∧ b.agree y := by
  change (∀ i, ∀ v ∈ a.sp i ⊔ b.sp i, images y i *ᵥ v = images x i *ᵥ v) ↔ _
  constructor
  · intro h
    exact ⟨fun i v hv => (h i v (Submodule.mem_sup_left hv)).trans (ha _ v hv),
      fun i v hv => (h i v (Submodule.mem_sup_right hv)).trans (hb _ v hv)⟩
  · rintro ⟨u,w⟩ i v hv
    obtain ⟨l,hl,r,hr,rfl⟩ := Submodule.mem_sup.mp hv
    rw [Matrix.mulVec_add,Matrix.mulVec_add,ha _ _ hl,hb _ _ hr,u _ _ hl,w _ _ hr]

def fee (N : ℕ) (ζ : ℝ) (t : ℕ) := bp (-(1-ζ)*t*N)
def Pin.clear (a : Pin p n N) (ζ : ℝ) (w : Wgt (UnitType p n N)) :=
  ∀ b : Pin p n N, pr w b.agree ≤ fee N ζ (planNew a.sp b.sp)

structure PeelCell (w r : Wgt (UnitType p n N)) (D ζ : ℝ) (K : ℕ)
    (S : Finset (UnitType p n N)) (a b : Pin p n N) : Prop where
  pos : 0 < pr w (fun x => x ∈ S)
  fixpin : ∀ x ∈ S, b.agree x
  extendsSp : a.sp ≤ b.sp
  bound : planRank b.sp ≤ planRank a.sp + K
  clear : b.clear ζ (onW w (fun x => x ∈ S))
  density x : onW w (fun x => x ∈ S) x ≤ bp ((D+K+1)*N) * r x

theorem heavy_leaf {r w : Wgt (UnitType p n N)}
    {D ζ : ℝ} (hz : 0 < ζ) (hz' : ζ < 1) (hn : 0 < N)
    (hR : ∀ a : Pin p n N, pr r a.agree ≤ fee N (ζ/4) (planRank a.sp))
    (hc : ∀ x, w x ≤ bp (D*N)*r x) (hw : ∀ x, 0 ≤ w x)
    (R : Finset (UnitType p n N)) (a : Pin p n N) (hf : ∀ x ∈ R, a.agree x)
    {K : ℕ} (hK : D + ζ ≤ (ζ-ζ/4)*K)
    (hpos : bp (-ζ*N) < pr w (fun x => x ∈ R)) :
    ∃ S : Finset (UnitType p n N), S ⊆ R ∧ ∃ b : Pin p n N,
      PeelCell w r D ζ K S a b := by
  classical
  have hn' : 0 < (N:ℝ) := by exact_mod_cast hn
  have hr : ∀ x, 0 ≤ r x := by
    intro x
    by_contra! h
    exact not_lt_of_ge ((hw x).trans (hc x)) (mul_neg_of_pos_of_neg (bp_pos _) h)
  let cut := bp (-ζ*N)
  let q (b : Pin p n N) := planNew a.sp b.sp
  let s (b : Pin p n N) : Finset (UnitType p n N) := R.filter b.agree
  let c (b : Pin p n N) := pr w (fun x => x ∈ s b)
  let heavy (b : Pin p n N) := a.sp ≤ b.sp ∧ cut * fee N ζ (q b) < c b
  let T := {t : ℕ | ∃ b, heavy b ∧ q b = t}
  have e1 : heavy a := by
    have ha : s a = R := by ext x; simp [s]; tauto
    refine ⟨le_rfl,?_⟩
    simpa only [q,planNew,sup_idem,Nat.sub_self,cut,c,ha,fee,Nat.cast_zero,
      mul_zero,zero_mul,bp_zero,mul_one] using hpos
  have bound (b : Pin p n N) (hh : heavy b) : q b ≤ K := by
    have hmo : (planRank b.sp : ℝ) ≥ q b := by
      have hg := plan_add_rank a.sp b.sp
      rw [sup_eq_right.mpr hh.1] at hg
      have hh' : q b ≤ planRank b.sp := by unfold q; omega
      exact_mod_cast hh'
    have he : cut * fee N ζ (q b) < bp (D*N) * fee N (ζ/4) (q b) := by
      refine hh.2.trans_le ?_
      calc
        c b ≤ pr w b.agree :=
          pr_mono hw (fun x h => (Finset.mem_filter.mp h).2)
        _ ≤ bp (D*N)* pr r b.agree := pr_cap hc _
        _ ≤ _ := mul_le_mul_of_nonneg_left ((hR b).trans (by
          unfold fee
          apply bp_le
          apply mul_le_mul_of_nonneg_right _ hn'.le
          exact mul_le_mul_of_nonpos_left hmo (by linarith))) (bp_pos _).le
    unfold cut fee at he
    rw [← bp_add,← bp_add] at he
    have hg (x y : ℝ) (h : bp x<bp y) : x<y := lt_of_not_ge (fun e =>
      not_lt_of_ge (bp_le e) h)
    have h' := hg _ _ he
    have hi : (ζ-ζ/4)*(q b:ℝ) < D+ζ := by
      apply (mul_lt_mul_iff_left₀ hn').mp
      linarith only [h']
    have hj := (mul_lt_mul_iff_right₀ (show 0 < ζ-ζ/4 by linarith)).mp (hi.trans_le hK)
    exact_mod_cast hj.le
  obtain ⟨b,hb,hT⟩ : ∃ b, heavy b ∧ q b = sSup T :=
    Nat.sSup_mem (show T.Nonempty from ⟨_,a,e1,rfl⟩)
      (show BddAbove T from ⟨K,fun t ⟨b,h,r⟩ => r ▸ bound b h⟩)
  have hcut := bp_pos (-ζ*N)
  have hmass : 0 < c b := (mul_pos hcut (bp_pos _)).trans hb.2
  let v := onW w (fun x => x ∈ s b)
  have hv : IsLaw v := normW_law (subW_nonneg hw _) hmass
  have hg := plan_add_rank a.sp b.sp
  rw [sup_eq_right.mpr hb.1] at hg
  have hp := bound b hb
  refine ⟨s b,Finset.filter_subset _ _,b,hmass,fun x h => (Finset.mem_filter.mp h).2,
    hb.1, ?_, fun B => ?_, fun x => ?_⟩
  · change planNew _ _ ≤ _ at hp
    omega
  · by_contra! he
    have hB := bp_pos (-(1-ζ)*(planNew b.sp B.sp)*N)
    change fee N ζ _ < pr v B.agree at he
    have he' := pr_of_on hw (fun x => x ∈ s b) B.agree
    change _ = c b * pr v B.agree at he'
    have hhpos : 0 < pr w (fun x => x ∈ s b ∧ B.agree x) :=
      he'.symm ▸ mul_pos hmass (lt_trans hB he)
    obtain ⟨x,⟨hx,hx'⟩,_⟩ := exists_of_pr_pos hw hhpos
    let J := Pin.make (b.sp⊔B.sp) x
    have hjoin : c J = c b * pr v B.agree := by
      have hxy (y) : y ∈ s J ↔ y ∈ s b ∧ B.agree y := by
        have hy := Pin.combine (Finset.mem_filter.mp hx).2 hx' (y:=y)
        change J.agree y ↔ b.agree y ∧ B.agree y at hy
        simp only [s,Finset.mem_filter,hy,and_assoc]
      simp_rw [← he',c,hxy]
    have hu : q b + planNew b.sp B.sp = q J := planNew_mono_add hb.1
    have hj : heavy J := by
      refine ⟨le_trans hb.1 le_sup_left, ?_⟩
      have hi :
          fee N ζ (q J) = fee N ζ (q b)* fee N ζ (planNew b.sp B.sp) := by
        unfold fee; rw [← bp_add,← hu]
        push_cast; ring_nf
      rw [hjoin,hi,← mul_assoc]
      apply lt_trans (mul_lt_mul_of_pos_right hb.2 hB)
      exact mul_lt_mul_of_pos_left he hmass
    have hd : 0 < planNew b.sp B.sp := by
      by_contra! hi
      rw [show planNew b.sp B.sp=0 from Nat.eq_zero_of_le_zero hi] at he
      have hh := pr_le_tot (p:=B.agree) hv.nz
      rw [hv.total] at hh
      simp only [fee,Nat.cast_zero,mul_zero,zero_mul,bp_zero] at he
      linarith
    have ha : q J ≤ sSup T := le_csSup
      (show BddAbove T from ⟨K,fun t ⟨b,h,r⟩ => r ▸ bound b h⟩)
      ⟨J,hj,rfl⟩
    omega
  · apply (on_mon hw (mul_pos hcut (bp_pos (-(1-ζ)*(q b)*N))) hb.2.le x).trans
    apply (mul_le_mul_of_nonneg_left (hc x) (inv_nonneg_of_nonneg (mul_pos hcut (bp_pos _)).le)).trans
    rw [← mul_assoc,← bp_add,← bp_neg,← bp_add]
    apply mul_le_mul_of_nonneg_right _ (hr x)
    apply bp_le
    have hk1 : 0 ≤ (q b:ℝ) := Nat.cast_nonneg _
    have hh : (q b:ℝ) ≤ K := by exact_mod_cast hp
    nlinarith only [mul_le_mul_of_nonneg_right hh hn'.le, mul_lt_mul_of_pos_right hz' hn',
      mul_nonneg hk1 (mul_pos hz hn').le]

theorem peel_family {r w : Wgt (UnitType p n N)}
    {D ζ : ℝ} (hz : 0 < ζ) (hz' : ζ < 1) (hn : 0 < N)
    (hR : ∀ a : Pin p n N, pr r a.agree ≤ fee N (ζ/4) (planRank a.sp))
    (hc : ∀ x, w x ≤ bp (D*N)*r x) (hw : ∀ x, 0 ≤ w x)
    (R : Finset (UnitType p n N)) (a : Pin p n N) (hf : ∀ x ∈ R, a.agree x)
    {K : ℕ} (hK : D + ζ ≤ (ζ-ζ/4)*K) :
    ∃ G : Finset (Finset (UnitType p n N)),
      (∀ S ∈ G, S⊆R ∧ ∃ b, PeelCell w r D ζ K S a b) ∧
      (∀ x, ∀ S ∈ G, ∀ J ∈ G, x∈S → x∈J → S=J) ∧
      pr w (fun x => x ∈ R ∧ ¬∃ S∈G,x∈S) ≤ bp (-ζ*N) := by
  classical
  induction R using Finset.strongInductionOn with | _ R ih
  by_cases hr : pr w (fun x => x∈R) ≤ bp (-ζ*N)
  · exact ⟨∅,by simpa using hr⟩
  obtain ⟨S,hS,b,hb⟩ := heavy_leaf hz hz' hn hR hc hw R a hf hK (lt_of_not_ge hr)
  have he := exists_of_pr_pos hw hb.pos
  obtain ⟨G,hG,hU,hW⟩ := ih (R\ S) (Finset.sdiff_ssubset hS
    (show S.Nonempty from ⟨he.choose,he.choose_spec.1⟩))
    (fun x h => hf x (Finset.mem_sdiff.mp h).1)
  refine ⟨insert S G, fun J h => ?_, fun x J h J' h' g g' => ?_,?_⟩
  · rcases Finset.mem_insert.mp h with rfl|h
    · exact ⟨hS,b,hb⟩
    · exact ⟨(hG J h).1.trans (Finset.sdiff_subset), (hG J h).2⟩
  · have hi (J) (h : J∈G) (g : x∈J) : x∉S := (Finset.mem_sdiff.mp ((hG J h).1 g)).2
    rcases Finset.mem_insert.mp h with h|h <;> rcases Finset.mem_insert.mp h' with h'|h'
    · rw [h,h']
    · exact ((hi _ h' g') (h ▸ g)).elim
    · exact ((hi _ h g) (h' ▸ g')).elim
    · exact hU _ _ h _ h' g g'
  · refine le_trans (pr_mono hw ?_) hW
    intro x h
    simp only [Finset.exists_mem_insert,not_or] at h
    exact ⟨Finset.mem_sdiff.mpr ⟨h.1,h.2.1⟩,h.2.2⟩

end HadwigerCounterexample

end

end OAI
