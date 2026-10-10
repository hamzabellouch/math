import OAI.Combinatorics.HadwigerCounterexample.FourCornerTrials

namespace OAI

/-! # Cut Integral Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real Matrix Function Filter
open scoped BigOperators Topology
variable {p : Shape} {n N M : ℕ} {I A : Type} [Fintype I] [DecidableEq I] [Fintype A]

def chairpan (p : I→Wgt A) (x : Bool×I) := p x.2
def reparse (I A : Type) : (Bool×I→ A)≃ (I→A) × (I→A) :=
  (show (_:Type)≃(Bool→I→A) from ⟨curry,uncurry,fun _=>rfl,fun _=>rfl⟩).trans (wingpair _)

theorem chairpan_law (p : I→Wgt A) :
    mapW (prodW (chairpan p)) (reparse I A)=pairW (prodW p) (prodW p) := by
  classical
  funext i
  obtain ⟨i,rfl⟩ := (reparse I A).surjective i
  rw [mapW_equiv_val,Equiv.symm_apply_apply]; unfold pairW prodW
  rw [Fintype.prod_prod_type,Fintype.prod_bool]; rfl
namespace Template
variable (v : Template p I)

def panels (v : Template p I) := collect p v (Prod.snd : Bool × I → I)
def rekeys (v : Template p I) (k : Keys (p:=p) v.panels.t N) :
    Keys (p:=p) v.t N ×Keys (p:=p) v.t N := (fun i=>k (true,i),fun i=>k (false,i))

def clue (v : Template p I) (j : I) (T : Wgt (Inputs p n I)) (U : Wgt (Keys (p:=p) v.t N))
    (x : Inputs p n (Bool × I)) (y : Keys (p:=p) v.panels.t N) :=
  quart (chairI v j n) T (reparse _ _ x)*quart (chairK v j N) U (rekeys v y)

theorem clue_crane (v : Template p I) (j : I) (T : Wgt (Inputs p n I)) (U : Wgt (Keys
    (p:=p) v.t N)) (w : I→ Wgt (Knobs p.g n)) :
    crane v j T U w=v.panels.sampleAll (chairpan w) (clue v j T U) := by
  classical
  funext i
  unfold crane; dsimp only
  rw [←chairpan_law w,mapW_avg]; unfold sampleAll
  refine avg_congr fun k hk => ?_
  rw [quart_prot]; rfl

def scene (v : Template p I) (T : Wgt (Inputs p n I)) (U : Wgt (Keys (p:=p) v.t N))
    (w f : I→ Wgt (Knobs p.g n)) (o : UnitType p n N) :=
  avg (prodW w) (fun x => protean v T U o x * prodW f x)

def blackout (v : Template p I) (T : Wgt (Inputs p n I)) (U : Wgt (Keys (p:=p) v.t N))
    (w : I→Wgt (Knobs p.g n)) (ε : ℝ) (o : UnitType p n N) :=
  ∃ f:I→Wgt (Knobs p.g n),(∀ i j,|f i j|≤1) ∧ ε < |scene v T U w f o|

theorem shaft (v : Template p I) (j : I) (U : Wgt (Keys (p:=p) v.t N))
    (T : Wgt (Inputs p n I)) (w f : I→ Wgt (Knobs p.g n)) (hw : ∀ i,IsLaw (w i))
    (hf : ∀ i j,|f i j|≤1) (o : UnitType p n N) :
    |scene v T U w f o|^4 ≤ crane v j T U w o := by
  classical
  let D (i : Aside j) := f i.val
  have h0 i : |prodW D i|≤1 := by
    unfold prodW; rw [abs_prod]; exact (prod_le_prod₀ (fun i _=>abs_nonneg _) (fun i _=>hf _ _)).trans_eq
                                       (by simp)
  have he (i : Inputs p n I) :
      prodW f i=f j (i j)*prodW D ((chairI v j n i).2) := chair_split f i j
  unfold scene; simp_rw [he]
  exact quart_CS (chairI v j n) _ _ _ _ (chair_weight w j) (hw j)
    (prodW_law fun i:Aside j=> hw i.val) (f j) (prodW D) (hf j) h0

set_option maxHeartbeats 1200000 in
theorem shade_calendar (v : Template p I) (j : I) (M : ℕ) (hM : 1≤M)
    (C ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ᶠ n : ℕ in atTop,
      let N := M*n
      ∀ (q : I→F) (U : Wgt (Keys (p:=p) v.t N)) (T : Wgt (Inputs p n I))
        (w : I→Wgt (Knobs p.g n)), (∀ x, |U x|≤1) → chairCut v j U δ →
        carried U (ownPart (p:=p) v.t q) →
        (∀ x, |T x|≤1) → (∀ i,IsLaw (w i)) →
        (∀ i,mapW (w i) (freePart p)=unif) →
      ∀ (m : Mixer p n), 2*num (Full p n)<N →
      let μ:=raw m N; let H:=bp ((1/32:ℝ)*n)
      ∀ (ρ : Wgt (UnitType p n N)), IsLaw ρ →
      (∀ x,mapW ρ Prod.fst x≤ H*μ x) → (∀ x,mapW ρ Prod.snd x≤ H*μ x) →
      (∀ x,ρ x ≤ bp (C*N)*pairW μ μ x) →
      pr ρ (blackout v T U w ε) ≤ bp (-(1/16:ℝ)*n) := by
  classical
  let E := ε^4/2; have hE : 0<E := by positivity
  let k := num v.PackSlot
  let W := netFact v.seam; have hW : 0<W := netFact_pos
  let d:=E/2/W
  have hd : 0<d := by positivity
  let f (N : ℕ) := 2*W * (num (Ports p)*(2*bp (k-N)))+W*(d+bp (-(N:ℝ)/2))
  let z (n : ℕ) := bp (num Bool*num I-n)
  have hh₁ : Tendsto (fun n:ℕ=>f (M*n)+z n) atTop (𝓝 (W*d)) := by
    have hh (c : ℝ) (C : ℝ) (hC : 0<C) {v : ℕ→ℝ} (hv : Tendsto v atTop atTop) :
        Tendsto (fun i => bp (c-C*v i)) atTop (𝓝 0) := by
      simp_rw [sub_eq_add_neg,bp_add, ← neg_mul]
      simpa using ((bp_tendsto_zero hC).comp hv).const_mul (bp c)
    let N (i : ℕ) := (↑(M*i):ℝ)
    have he := cast_tops M hM
    have hz := hh (num Bool*num I) 1 zero_lt_one (v:=fun n:ℕ=>(n:ℝ)) tendsto_natCast_atTop_atTop
    have h1 := hh k 1 zero_lt_one he
    have h2 : Tendsto (fun i => bp (-N i/2)) atTop (𝓝 0) := by
      have hq := hh 0 (1/2) (by norm_num) he
      refine (tendsto_congr' ?_).mp hq
      exact .of_forall (fun n => by unfold N; simp only [zero_sub]; congr 1; ring)
    have h3 := (((h1.const_mul 2).const_mul (num (Ports p))).const_mul (2*W)).add
      ((h2.const_add d).const_mul W)
    simpa only [mul_zero,zero_add,add_zero,f,z,N,one_mul] using h3.add hz
  have hh₂ : W*d<E := by unfold d; field_simp; linarith only [hE]
  refine ⟨d,hd,?_⟩
  filter_upwards [typical_calendar v.panels M hM C E hE,
    hh₁.eventually (gt_mem_nhds hh₂),(cast_tops M hM).eventually (eventually_ge_atTop (2*k+1))]
    with n hn hq he N q U T w hU hx hP hT hw hz m hN μ H ρ hρ h1 h2 h3
  have hk : 2*k-N ≤ -1 := by
    change 2*k+1 ≤ (N:ℝ) at he
    linarith only [he]
  have hm := crane_mean v j q U T w hw hz m hN d hd.le hU hT hx hP k
    (port_limit v.seam) hk
  have hi (x y) : |clue v j T U x y|≤1 := by
    unfold clue; rw [abs_mul]
    exact (mul_le_mul (quart_bound T hT _ _) (quart_bound U hU _ _)
      (abs_nonneg _) zero_le_one).trans_eq (by norm_num)
  let g := crane v j T U w
  have h4 := hn m ρ hρ h1 h2 h3 hN (chairpan w) (fun i=>hw i.2)
    (fun i=>hz i.2) _ hi
  change pr ρ _ ≤ _ at h4
  have hh (x) : (panels v).sampleAll (chairpan w) (clue v j T U) x=g x :=
    Eq.symm (congr_fun (clue_crane ..) x)

  have hh' : (panels v).sampleAll (chairpan w) (clue v j T U)=g := funext hh
  change pr ρ (fun x => E≤ |(panels v).sampleAll (chairpan w) (clue v j T U) x-
    avg (pairW μ μ) ((panels v).sampleAll (chairpan w) (clue v j T U))|)≤_ at h4
  rw [hh'] at h4
  apply (pr_mono hρ.nz ?_).trans h4
  rintro i ⟨b,hb,hv⟩
  have ht := shaft v j U T w b hw hb i
  have hG : avg (pairW μ μ) g ≤ E := (le_abs_self _).trans (hm.trans hq.le)
  have hy : ε^4 ≤ g i := (pow_le_pow_left₀ hε.le hv.le 4).trans ht
  exact le_trans (show E ≤ g i-avg (pairW μ μ) g from by unfold E at *; linarith only [hG,hy])
    (le_abs_self _)
end Template
end HadwigerCounterexample

end

end OAI
