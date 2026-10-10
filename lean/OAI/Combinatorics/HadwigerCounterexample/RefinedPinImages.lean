import OAI.Combinatorics.HadwigerCounterexample.PartitionSelection
import OAI.Combinatorics.HadwigerCounterexample.FourPhaseBits

namespace OAI

/-! # Refined Pin Images -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

def front (s : Plan p n) : Plan p n := prSmall s

theorem front_rank (s : Plan p n) : planRank (front s) ≤2*planRank s := by
  classical
  unfold planRank
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hh (j) :
      dim ((sPin s i j).map (IP p n j).mulVecLin)≤dim (s i) :=
    (Submodule.finrank_map_le ..).trans (sPin_dim ..)
  exact ((Submodule.finrank_add_le_finrank_add_finrank ..).trans (add_le_add (hh _) (hh _))).trans_eq
    (two_mul _).symm

theorem combined_rank (s t : Plan p n) : planRank (s⊔t)≤planRank s+planRank t := by
  unfold planRank; rw [←Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => finrank_add_le_finrank_add_finrank ..

abbrev Signal (p : Shape) (N : ℕ) {n} (s : Plan p n) := DTuple (p:=p) (fun z => dim (s z)) N

def readPin (x : UnitType p n N) (a : Plan p n) : Signal p N a :=
  fun z => images x z * pack (a z)

abbrev EffSeq {p : Shape} {n} (s : Plan p n) := ∀ i : Bool,effective s i

def entrySeq {p : Shape} {n} (s : Plan p n) (m : Bool → Profile p n) : EffSeq s :=
  open scoped Classical in
  fun i => if h : m i ∈ effective s i then ⟨_,h⟩ else 0

abbrev Story {p : Shape} {n N} (T : Cov p N) (s : Plan p n) :=
  Daypair p T × Signal p N (front s) × EffSeq s

instance fintypeStory {s : Plan p n} {T : Cov p N} : Fintype (Story T s) := by
  classical
  let A := (coverX p T)
  letI : Finite (Module.Dual F A) := Finite.of_injective _ DFunLike.coe_injective
  letI : Fintype (Module.Dual F A) := Fintype.ofFinite _
  letI : Fintype (Daypair p T) := inferInstanceAs (Fintype (Daypair p T))
  letI : ∀ i,Fintype (effective s i) := fun i => Fintype.ofFinite _
  letI : Fintype (EffSeq s) := inferInstanceAs (Fintype (EffSeq s))
  letI : Fintype (Signal p N (front s)) := inferInstanceAs (Fintype (Signal p N (front s)))
  exact inferInstanceAs (Fintype (Story T s))

def story (T : Cov p N) (s : Plan p n) (m : BMark p n N) (x : UnitType p n N) : Story T s :=
  (daypair p T (delta m) (fun _ => 1) x,readPin x (front s),entrySeq s (m x))

def specialLeaf (T : Cov p N) (m : BMark p n N) (a : Pin p n N)
    (G : CTile p n N) (b : Pin p n N) :=
  a.sp ≤ b.sp ∧ front a.sp ≤ b.sp ∧
    ∀ x∈G,∀ y∈G, m x=m y ∧ delta m x=delta m y ∧
      ∀ i,juris p T x (unary i) = juris p T y (unary i)

private theorem storyOk (T : Cov p N) (m : BMark p n N)
    (a : Pin p n N) (S : CTile p n N) (K : ℕ) (hk : planRank a.sp≤K)
    (h : ∀ x∈S, a.agree x ∧ covered p T (delta m x) ∧
       ∀ i,m x i∈effective a.sp i) :
    ∀ i : Story T a.sp,∃ b : Pin p n N,
       (∀ x∈ S,story T a.sp m x=i → b.agree x) ∧ planRank b.sp ≤ 3*K ∧
       ∀ c (G : CTile p n N), G.Nonempty →
         (∀ x∈G,x∈S ∧ story T a.sp m x=i) → b.sp ≤ c.sp → specialLeaf T m a G c := by
  classical
  intro i
  let A := a.sp ⊔ front a.sp
  have hK : planRank A≤3*K := by
    apply (combined_rank ..).trans
    have hh := front_rank a.sp
    omega
  have h1 : ∃ x : UnitType p n N, ∀ y∈ S,story T a.sp m y=i → (Pin.make A x).agree y := by
    by_cases hg : ∃ x∈S,story T a.sp m x=i
    · obtain ⟨x,hx,he⟩ := hg
      refine ⟨x,fun y hy ht => ?_⟩
      let b := Pin.make (front a.sp) x
      have hf : b.agree y := by
        rw [Pin.agree_pack]; intro z
        have hh : readPin y (front a.sp)=readPin x (front a.sp) :=
          congrArg (fun x : Story T a.sp => x.2.1) (ht.trans he.symm)
        exact congr_fun hh z
      exact (Pin.combine (b:=b) (h x hx).1 (show b.agree x from fun _ _ _ => rfl)).mpr
        ⟨(h y hy).1,hf⟩
    exact ⟨0,fun x hx he => (hg ⟨x,hx,he⟩).elim⟩
  obtain ⟨x,hx⟩ := h1
  refine ⟨Pin.make A x,hx,hK,fun c G hm hC hA => ⟨le_trans le_sup_left hA,
    le_trans le_sup_right hA, fun x hx y hy => ?_⟩⟩
  have he := (hC x hx).2.trans (hC y hy).2.symm
  have hD := congrArg Prod.fst he
  have hr z (hz : z∈G) : (story T a.sp m z).1.1.val=delta m z := by
    unfold story daypair; change (cutDown p T (delta m) (fun _ => 1) z).val=_
    unfold cutDown; rw [dite_eq_left ⟨(by norm_num),(h z (hC z hz).1).2.1⟩]
  have ht z (hz : z∈G) (i) : ((story T a.sp m z).2.2 i).val=m z i := by
    unfold story entrySeq; dsimp only
    rw [dite_eq_left ((h z (hC z hz).1).2.2 i)]
  refine ⟨funext (fun i => ?_),?_,fun i => ?_⟩
  · rw [←ht x hx i,←ht y hy i,he]
  · rw [←hr x hx, ←hr y hy,he]
  exact congr_fun (congrArg Prod.snd hD) i

theorem story_size (T : Cov p N) (s : Plan p n) (K d : ℕ)
    (hK : planRank s≤K) (hd : cdim p T≤d) :
    num (Story T s) ≤ bp ((3*d+2*K : ℝ)*N + 2*K^2) := by
  classical
  have h1 : dim (coverX p T)≤ N*d := (cover_dim p T).trans (Nat.mul_le_mul_left N hd)
  have h2 : dim (Daypair p T) ≤ 3*d*N := by
    unfold dim Daypair
    rw [finrank_prod,finrank_pi_fintype, Fintype.sum_bool,Subspace.dual_finrank_eq]
    change dim _+(dim _+dim _) ≤ _
    nlinarith
  have h3 : dim (Signal p N (front s)) ≤ (2*K)*N := tuple_dim.trans_le (by
    rw [mul_comm]; apply Nat.mul_le_mul_right
    exact (front_rank s).trans (Nat.mul_le_mul_left _ hK))
  have h4 : dim (EffSeq s)≤ 2*K^2 := by
    unfold EffSeq dim
    rw [finrank_pi_fintype,Fintype.sum_bool,two_mul]
    have hh i : dim (effective s i) ≤ K^2 := (effective_dim ..).trans (by gcongr)
    exact add_le_add (hh _) (hh _)
  unfold num
  rw [card_space]
  apply bp_le
  have hh : dim (Story T s)≤ (3*d+2*K)*N+2*K^2 := by
    unfold Story dim; rw [finrank_prod, finrank_prod (M:=Signal p N (front s))]
    change dim (Daypair p T)+(dim (Signal p N (front s))+dim (EffSeq s)) ≤ _
    rw [Nat.add_mul,add_assoc]
    exact add_le_add h2 (add_le_add h3 h4)
  exact_mod_cast hh

theorem plan_inc_eff (s t : Plan p n) (h : s ≤ t) (i : Bool) :
    effective s i≤effective t i := by
  intro x hx
  obtain ⟨h1,h2⟩ := effective_mem.mp hx
  have he z : sPin s z i ≤ sPin t z i := Submodule.map_mono (h z)
  exact effective_mem.mpr ⟨h1,fun z => box_le (he _) (he _) (h2 _)⟩

/-- Old contractions on admissible tables evaluate correctly when
the enlarged leaf has pinned the entire front. -/
theorem front_table (x y : UnitType p n N)
    {a b : Pin p n N} (s : Plan p n)
    (hf : front s≤a.sp)
    {M : Cross p n} (hx : a.agree x) (hB : tableFlag b a (reciprocal p M) y)
    (i j : Bool) (w : Profile p n) (h : w∈effective s i) :
    contract p (actual p x y) i j w=contract p M i j w := by
  have hz (z) (u : Dir p n) (hu : u∈a.sp z) :
      channelOut p M j z *ᵥ u=channelOut p (actual p x y) j z *ᵥ u := by
    refine channel_same j z u (fun v => ?_)
    have h1 : IH p n j *ᵥ v∈tabSpace b.sp (flipZ p z) :=
      channel_le_table b.sp _ _ ⟨_,rfl⟩
    have h2 : u∈a.sp (flipZ p (flipZ p z)) := by rwa [flipZ_flip]
    have he := hB (flipZ p z) _ h1 _ h2
    have hg := flag_actual (a:=b) y x hx (flipZ p z) _ h1 _ h2
    rw [← reciprocal_actual x y] at hg
    simp only [reciprocal,flipZ_flip,evmat_transpose] at he hg
    exact he.trans hg.symm
  have he z : (sPin s z i).map (IP p n i).mulVecLin ≤ a.sp z := by
    apply le_trans _ (hf z)
    cases i; exact le_sup_right; exact le_sup_left
  change ∑ e, _=_
  refine Finset.sum_congr rfl fun e _ => ?_
  refine (box_eval_iff (a.sp (e,true)) (a.sp (e,false)) _ _).mp ?_ _
    (box_le (he _) (he _) (lift_mem_box _ _ ((effective_mem.mp h).2 e)))
  intro x hx y hy
  rw [ev_duom,ev_duom,hz _ _ hx,hz _ _ hy]

set_option maxHeartbeats 900000 in
theorem weave (P : UnitType p n N→Prop)
    {w μ : Wgt (UnitType p n N)}
    (m : BMark p n N) (T : Cov p N)
    (hw : ∀ x,0≤w x) {D ζ u : ℝ} (hz : 0 < ζ) (hz' : ζ<1) {K K' d : ℕ}
    (hn : 0<N)
    (hμ : ∀ a : Pin p n N,pr μ a.agree ≤ fee N (ζ/4) (planRank a.sp))
    (hd : cdim p T≤d)
    {F : Canopy p n N} (hT : apart F) (g : CTile p n N → Pin p n N)
    (h : ∀ i∈F,Ripe p w μ i (g i) D ζ K)
    (hg : ∀ i∈ F,∀ x∈i,P x→covered p T (delta m x) ∧ ∀ j,m x j∈effective (g i).sp j)
    (hk : D+u+ζ≤(ζ-ζ/4)*K')
    (hu : (3*d+2*K:ℝ)*N+2*K^2 ≤ (u-1)*N) :
    ∃ V : Canopy p n N,apart V ∧
    (∀ S∈V,∃ i∈F,S⊆i ∧ (∀ x∈ S,P x) ∧
      ∃ b : Pin p n N,Ripe p w μ S b (D+u+K'+1) ζ (3*K+K') ∧ specialLeaf T m (g i) S b) ∧
    pr w (fun x => inTiles F x ∧ P x ∧ ¬inTiles V x) ≤
      allMass w F*(bp (-(N:ℝ))+bp (-ζ*N)) := by
  classical
  refine improve F w hw P
    (fun i S => (∀ x∈ S,P x) ∧ ∃ b : Pin p n N,Ripe p w μ S b (D+u+K'+1) ζ (3*K+K') ∧
      specialLeaf T m (g i) S b)
    hT (fun i hi => ?_)
  let A := CTile p n N
  let S := i.filter P
  let Q := specialLeaf T m (g i)
  have hs (x : UnitType p n N) : x∈S↔ x∈i∧ P x := Finset.mem_filter
  have hq := h i hi
  let w' := partW w i
  have hw' : IsLaw w' := on_law hw hq.pos
  have hg : ∀ x∈ S,(g i).agree x∧ covered p T (delta m x)∧∀ j,m x j∈effective (g i).sp j :=
    fun x h => ⟨hq.fixpin _ ((hs ..).mp h).1,hg i hi x ((hs ..).mp h).1 ((hs ..).mp h).2⟩
  obtain ⟨V,hV,hX,hZ⟩ := reparts w' μ hw' S D ζ u hn hz hz' hμ hq.density
    (story T (g i).sp m) (3*K) K' Q
    (storyOk T m (g i) S K hq.bound hg) hk
  refine ⟨V,hV,fun x hx => ?_,?_⟩
  · obtain ⟨hS,b,hB,hL⟩ := hX x hx
    have hx' : x⊆i := hS.trans (Finset.filter_subset ..)
    obtain ⟨he,hLaw⟩ := issued_law w hw hq.pos hx' hB.pos
    refine ⟨hx', (fun z hz => ((hs ..).mp (hS hz)).2),b,⟨he,hB.fixpin,hB.bound,?_,?_⟩,hL⟩
    · rw [hLaw]; exact hB.clear
    rw [hLaw]; exact hB.density
  simp_rw [hs,and_assoc] at hZ
  refine hZ.trans (add_le_add_left ?_ _)
  refine (mul_le_mul_of_nonneg_right (story_size T _ K d hq.bound hd) (bp_pos _).le).trans ?_
  rw [←bp_add]; apply bp_le
  linarith only [hu]

theorem phase_fixed (m : BMark p n N) (T : Cov p N)
    (A A' B B' : Pin p n N) {S R : CTile p n N}
    {x x' y y' : UnitType p n N}
    (h : specialLeaf T m A S A') (hg : specialLeaf T m B R B')
    (hx : x∈S) (hx' : x'∈S) (hy : y∈R) (hy' : y'∈R)
    (hC : covered p T (delta m x)) (hC' : covered p T (delta m y)) :
    quench p (delta m) (x,y)=quench p (delta m) (x',y') := by
  obtain ⟨_,h1,h2⟩ := h.2.2 x hx x' hx'
  obtain ⟨_,h3,h4⟩ := hg.2.2 y hy y' hy'
  unfold quench; dsimp only
  rw [← h1, ← h3]
  exact Prod.ext
    (funext fun i => LinearMap.congr_fun (h4 i) (⟨_,hC⟩ : coverX p T))
    (funext fun i => LinearMap.congr_fun (h2 i) (⟨_,hC'⟩ : coverX p T))

end HadwigerCounterexample

end

end OAI
