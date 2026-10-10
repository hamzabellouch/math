import OAI.Combinatorics.HoneycombChords.Flux

namespace OAI

/-!
# Boundary flux estimates

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

namespace CriticalHoneycomb.Transfer.PlanarNormalization
open scoped BigOperators

/-- Positive combinations of genuine planar tensor diagrams. -/
inductive PositiveSpan (n b : ℕ) (seed : State) : DiluteState → Prop
  | zero : PositiveSpan n b seed (fun _=>0)
  | basis (o : List Bool) (k : ℕ) (w : PlanarWord b k)
      (hl : o.length=n) (hc : o.count true=b+2*k) :
      PositiveSpan n b seed (embed o (w.eval seed))
  | add {F G : DiluteState} (hF : PositiveSpan n b seed F)
      (hG : PositiveSpan n b seed G) : PositiveSpan n b seed (fun xs=>F xs+G xs)
  | smul (a : ℝ) (ha : 0≤a) {F : DiluteState} (hF : PositiveSpan n b seed F) :
      PositiveSpan n b seed (fun xs=>(a:ℂ)*F xs)

noncomputable def realWeights (a h v c d : ℝ) : TileWeights :=
  ⟨a,h,v,c,d⟩

lemma act_positive {a h v c d : ℝ} (ha : 0≤a) (hh : 0≤h) (hv : 0≤v)
    (hc : 0≤c) (hd : 0≤d) {n b i : ℕ} (hb : b≤1) (hi : i+1<n)
    {seed : State} {F : DiluteState} (hF : PositiveSpan n b seed F) :
    PositiveSpan n b seed (act (realWeights a h v c d) i F) := by
  induction hF with
  | zero => rw [act_zero]; exact .zero
  | add hF hG ihF ihG => rw [act_add]; exact .add ihF ihG
  | smul a ha hF ihF => rw [act_smul]; exact .smul a ha ihF
  | basis o k w hl hcount =>
    obtain ⟨pre,x,y,post,rfl,hpre⟩ := two_at o i (by omega)
    subst i
    cases x <;> cases y
    · rw [act_empty_at]
      apply PositiveSpan.add (.basis _ k w hl hcount)
      apply PositiveSpan.smul h hh
      have hip : pre.count true ≤ b+2*k := by simp [List.count_append] at hcount; omega
      exact .basis _ (k+1) (.insert w (pre.count true) hip)
        (by simpa using hl) (by simp_all [List.count_append]; omega)
    · rw [act_right_at]
      exact .add (.smul a ha (.basis _ k w hl hcount))
        (.smul v hv (.basis _ k w (by simpa using hl)
          (by simpa [List.count_append,List.count_cons] using hcount)))
    · rw [act_left_at]
      exact .add (.smul a ha (.basis _ k w hl hcount))
        (.smul v hv (.basis _ k w (by simpa using hl)
          (by simpa [List.count_append,List.count_cons] using hcount)))
    · have hk : 0<k := by simp [List.count_append] at hcount; omega
      obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
      have hip : pre.count true ≤ b+2*k := by simp [List.count_append] at hcount ⊢; omega
      rw [act_full_at]
      apply PositiveSpan.add
      · apply PositiveSpan.add
        · exact .smul c hc (.basis _ (k+1) w hl hcount)
        · apply PositiveSpan.smul h hh
          exact .basis _ k (.erase w (pre.count true) hip) (by simpa using hl)
            (by simp [List.count_append] at hcount ⊢; omega)
      · apply PositiveSpan.smul d hd
        exact .basis _ (k+1) (.insert (.erase w (pre.count true) hip) (pre.count true) hip) hl hcount

/-- Nonnegative multiples of an exact endpoint phase. -/
def PhasePositive (z q : ℂ) : Prop := ∃ a : ℝ, 0≤a ∧ z=(a:ℂ)*q
lemma PhasePositive.zero (q : ℂ) : PhasePositive 0 q := ⟨0,le_rfl,by simp⟩
lemma PhasePositive.add {z w q : ℂ} (hz : PhasePositive z q) (hw : PhasePositive w q) :
    PhasePositive (z+w) q := by
  obtain ⟨a,ha,rfl⟩ := hz; obtain ⟨b,hb,rfl⟩ := hw
  exact ⟨a+b,add_nonneg ha hb,by push_cast; ring⟩
lemma PhasePositive.smul {z q : ℂ} (hz : PhasePositive z q) {a : ℝ} (ha : 0≤a) :
    PhasePositive ((a:ℂ)*z) q := by
  obtain ⟨b,hb,rfl⟩ := hz
  exact ⟨a*b,mul_nonneg ha hb,by push_cast; ring⟩

lemma one_orientation_positive {n : ℕ} {F : DiluteState} {seed : State}
    (hF : PositiveSpan n 1 seed F) {xs : List Spin} {a : Bool}
    (hxs : orientations xs=[a]) (hs : PhasePositive (seed [a]) 1) :
    PhasePositive (F xs) 1 := by
  induction hF with
  | zero => exact .zero _
  | add hF hG ihF ihG => exact ihF.add ihG
  | smul a ha hF ihF => exact ihF.smul ha
  | basis o k w hl hc =>
    by_cases ho : occupancy xs=o
    · have hx := orientations_length xs
      rw [hxs,ho] at hx
      have hk : k=0 := by simp at hx; omega
      subst k
      obtain hw|hw := one_strand_zero_or_identity w seed
      · simp only [embed,ho,ite_true,hxs,hw]; exact .zero _
      · simpa only [embed,ho,ite_true,hxs,hw] using hs
    · simp only [embed,ho,ite_false]; exact .zero _

lemma two_orientation_positive {n : ℕ} {F : DiluteState}
    (hF : PositiveSpan n 0 (fun _=>1) F) {xs : List Spin} {a b : Bool}
    (hxs : orientations xs=[a,b]) : PhasePositive (F xs) (cup a b) := by
  induction hF with
  | zero => exact .zero _
  | add hF hG ihF ihG => exact ihF.add ihG
  | smul a ha hF ihF => exact ihF.smul ha
  | basis o k w hl hc =>
    by_cases ho : occupancy xs=o
    · have hx := orientations_length xs
      rw [hxs,ho] at hx
      have hk : k=1 := by simp at hx; omega
      subst k
      obtain ⟨r,hr⟩ := word_normal_form (by omega : 0≤1) w (fun _=>1)
      have he := hr [a,b] (by simp)
      cases r with
      | none => simp only [optionEval] at he
                simp only [embed,ho,ite_true,hxs,he]; exact .zero _
      | some ch =>
        cases ch with
        | insert ch i hi =>
          have hi0 : i=0 := by omega
          subst i
          cases ch
          simp [optionEval,CupHistory.eval,create] at he
          refine ⟨1,by positivity,?_⟩
          simpa [embed,ho,hxs] using he
    · simp only [embed,ho,ite_false]; exact .zero _

end CriticalHoneycomb.Transfer.PlanarNormalization

namespace CriticalHoneycomb.Transfer.PlanarNormalization
open scoped BigOperators

noncomputable def pointState (xs : List Spin) : DiluteState :=
  fun ys=>if ys=xs then 1 else 0

noncomputable def finitePair : ℕ → DiluteState → DiluteState → ℂ
  | 0,f,g => f [] * g []
  | n+1,f,g => ∑ x : Spin, finitePair n (fun xs=>f (x::xs)) (fun xs=>g (x::xs))

lemma finitePair_comm (n : ℕ) (f g : DiluteState) : finitePair n f g=finitePair n g f := by
  induction n generalizing f g with
  | zero => simp [finitePair,mul_comm]
  | succ n ih => simp only [finitePair,ih]

lemma finitePair_zero (n : ℕ) (f : DiluteState) : finitePair n (fun _=>0) f=0 := by
  induction n generalizing f with
  | zero => simp [finitePair]
  | succ n ih => simp [finitePair,ih]
lemma finitePair_scalar (n : ℕ) (a : ℂ) (f g : DiluteState) :
    finitePair n (fun xs=>a*f xs) g=a*finitePair n f g := by
  induction n generalizing f g with
  | zero => simp [finitePair,mul_assoc]
  | succ n ih => simp only [finitePair,ih,Finset.mul_sum]
lemma finitePair_sum {ι : Type*} [Fintype ι] (n : ℕ) (f : ι → DiluteState) (g : DiluteState) :
    finitePair n (fun xs=>∑ i,f i xs) g=∑ i,finitePair n (f i) g := by
  induction n generalizing f g with
  | zero => simp [finitePair,Finset.sum_mul]
  | succ n ih =>
    simp only [finitePair,ih]
    exact Finset.sum_comm
lemma finitePair_scalar_right (n : ℕ) (a : ℂ) (f g : DiluteState) :
    finitePair n f (fun xs=>a*g xs)=a*finitePair n f g := by
  rw [finitePair_comm,finitePair_scalar,finitePair_comm n g f]
lemma finitePair_sum_right {ι : Type*} [Fintype ι] (n : ℕ) (f : DiluteState) (g : ι → DiluteState) :
    finitePair n f (fun xs=>∑ i,g i xs)=∑ i,finitePair n f (g i) := by
  rw [finitePair_comm,finitePair_sum]
  simp only [finitePair_comm n f]

lemma pointState_cons (a : Spin) (xs : List Spin) (b : Spin) :
    (fun ys=>pointState (a::xs) (b::ys)) =
      if b=a then pointState xs else (fun _=>0) := by
  funext ys
  by_cases h : b=a <;> simp [pointState,h]
lemma finitePair_point (xs : List Spin) (g : DiluteState) :
    finitePair xs.length (pointState xs) g=g xs := by
  induction xs generalizing g with
  | nil => simp [finitePair,pointState]
  | cons a xs ih =>
    change (∑ b : Spin, finitePair xs.length
      (fun ys=>pointState (a::xs) (b::ys)) (fun ys=>g (b::ys))) = _
    calc
      _ = ∑ b : Spin, if b=a then g (b::xs) else 0 := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [pointState_cons]
        by_cases h : b=a <;> simp [h,finitePair_zero,ih]
      _ = _ := by simp
lemma finitePair_point_right (xs : List Spin) (g : DiluteState) :
    finitePair xs.length g (pointState xs)=g xs := by
  rw [finitePair_comm,finitePair_point]

lemma tile_transpose (t : TileWeights) (x y a b : Spin) : tile t x y a b=tile t a b x y := by
  cases x <;> cases y <;> cases a <;> cases b <;>
    simp [tile,eq_comm] ; ring

lemma finitePair_act_zero (t : TileWeights) (n : ℕ) (f g : DiluteState) :
    finitePair (n+2) (act t 0 f) g=finitePair (n+2) f (act t 0 g) := by
  simp only [finitePair,act,finitePair_sum,finitePair_scalar,
    finitePair_sum_right,finitePair_scalar_right]
  calc
    _ = ∑ a : Spin, ∑ b : Spin, ∑ x : Spin, ∑ y : Spin,
        tile t x y a b * finitePair n (fun xs=>f (a::b::xs)) (fun xs=>g (x::y::xs)) := by
      calc
        _ = ∑ x : Spin, ∑ a : Spin, ∑ y : Spin, ∑ b : Spin,
            tile t x y a b * finitePair n (fun xs=>f (a::b::xs)) (fun xs=>g (x::y::xs)) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact Finset.sum_comm
        _ = ∑ a : Spin, ∑ x : Spin, ∑ y : Spin, ∑ b : Spin,
            tile t x y a b * finitePair n (fun xs=>f (a::b::xs)) (fun xs=>g (x::y::xs)) := Finset.sum_comm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro a ha
          calc
            _ = ∑ x : Spin, ∑ b : Spin, ∑ y : Spin,
                tile t x y a b * finitePair n (fun xs=>f (a::b::xs)) (fun xs=>g (x::y::xs)) := by
              apply Finset.sum_congr rfl
              intro x hx
              exact Finset.sum_comm
            _ = _ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      rw [tile_transpose]

lemma finitePair_act (t : TileWeights) {n i : ℕ} (hi : i+1<n) (f g : DiluteState) :
    finitePair n (act t i f) g=finitePair n f (act t i g) := by
  induction i generalizing n f g with
  | zero =>
    obtain ⟨n,rfl⟩ : ∃ k,n=k+2 := ⟨n-2,by omega⟩
    exact finitePair_act_zero t n f g
  | succ i ih =>
    cases n with
    | zero => omega
    | succ n =>
      simp only [finitePair,act]
      apply Finset.sum_congr rfl
      intro a ha
      exact ih (by omega) _ _

noncomputable def gates (t : TileWeights) (gs : List ℕ) (f : DiluteState) : DiluteState :=
  gs.foldl (fun f i=>act t i f) f

lemma gates_append (t : TileWeights) (gs hs : List ℕ) (f : DiluteState) :
    gates t (gs++hs) f=gates t hs (gates t gs f) := by
  simp [gates,List.foldl_append]

lemma finitePair_gates (t : TileWeights) {n : ℕ} (gs : List ℕ)
    (hg : ∀ i∈gs,i+1<n) (f g : DiluteState) :
    finitePair n (gates t gs f) g=finitePair n f (gates t gs.reverse g) := by
  induction gs generalizing f g with
  | nil => rfl
  | cons i gs ih =>
    rw [show gates t (i::gs) f=gates t gs (act t i f) from rfl,
      ih (by aesop),finitePair_act t (hg i (by simp))]
    simp only [List.reverse_cons,gates,List.foldl_append,List.foldl_cons,List.foldl_nil]

/-- Ordinary transpose, not the Hermitian adjoint: precisely the cup gauge. -/
theorem gates_kernel_transpose (t : TileWeights) {n : ℕ} (gs : List ℕ)
    (hg : ∀ i∈gs,i+1<n) (xs ys : List Spin) (hx : xs.length=n) (hy : ys.length=n) :
    gates t gs (pointState xs) ys=gates t gs.reverse (pointState ys) xs := by
  have hp := finitePair_gates t gs hg (pointState xs) (pointState ys)
  rw [←hy,finitePair_point_right] at hp
  rw [hy,←hx,finitePair_point] at hp
  exact hp

lemma gates_positive {a h v c d : ℝ} (ha : 0≤a) (hh : 0≤h) (hv : 0≤v)
    (hc : 0≤c) (hd : 0≤d) {n b : ℕ} (hb : b≤1) (gs : List ℕ)
    (hg : ∀ i∈gs,i+1<n) {seed : State} {f : DiluteState}
    (hf : PositiveSpan n b seed f) :
    PositiveSpan n b seed (gates (realWeights a h v c d) gs f) := by
  induction gs generalizing f with
  | nil => exact hf
  | cons i gs ih =>
    exact ih (by aesop) (act_positive ha hh hv hc hd hb (hg i (by simp)) hf)

lemma point_one_positive (xs : List Spin) (a : Bool) (hxs : orientations xs=[a]) :
    PositiveSpan xs.length 1 (fun ys=>if ys=[a] then 1 else 0) (pointState xs) := by
  unfold pointState
  rw [←embed_delta,hxs]
  apply PositiveSpan.basis _ 0 .start
  · simp [occupancy]
  · have h := orientations_length xs
    rw [hxs] at h
    simpa using h.symm

lemma point_vacuum_positive (n : ℕ) :
    PositiveSpan n 0 (fun _=>1) (pointState (List.replicate n none)) := by
  have he : pointState (List.replicate n none)=embed (List.replicate n false) (fun _=>1) := by
    funext xs
    simp only [pointState,embed,]
    congr 1
    apply propext
    constructor
    · rintro rfl; simp [occupancy]
    · intro h
      have he : occupancy xs=occupancy (List.replicate n none) := by simpa [occupancy] using h
      apply occupancy_orientations_injective he
      have hh := orientations_length xs
      rw [h] at hh
      have hz : orientations xs=[] := List.length_eq_zero_iff.mp (by simpa [List.count_replicate] using hh)
      rw [hz]
      simp [orientations]
  rw [he]
  exact .basis _ 0 .start (by simp) (by simp [List.count_replicate])

end CriticalHoneycomb.Transfer.PlanarNormalization

namespace CriticalHoneycomb.Transfer.FluxWard
open scoped BigOperators
namespace Diagram
open PlanarNormalization

def rowSites : ℕ → ℕ → List ℕ
  | _,0 => []
  | i,h+1 => i::rowSites (i+1) h
def rectangleSites : ℕ → ℕ → List ℕ
  | 0,_ => []
  | w+1,h => rowSites w h++rectangleSites w h
lemma rowSites_valid {N i h : ℕ} (hi : i+h<N) :
    ∀ j∈rowSites i h,j+1<N := by
  induction h generalizing i with
  | zero => simp [rowSites]
  | succ h ih =>
    intro j hj
    simp only [rowSites,List.mem_cons] at hj
    rcases hj with rfl|hj
    · omega
    · exact ih (by omega) _ hj
lemma rectangleSites_valid {N w h : ℕ} (hi : w+h≤N) :
    ∀ j∈rectangleSites w h,j+1<N := by
  induction w with
  | zero => simp [rectangleSites]
  | succ w ih =>
    intro j hj
    simp only [rectangleSites,List.mem_append] at hj
    rcases hj with hj|hj
    · exact rowSites_valid (by omega) _ hj
    · exact ih (by omega) _ hj
lemma decode_row (i h : ℕ) (f : FState) :
    decode (rowAct i h f)=gates physicalWeights (rowSites i h) (decode f) := by
  induction h generalizing i f with
  | zero => rfl
  | succ h ih =>
    simp only [rowAct,rowSites,gates,List.foldl_cons]
    rw [ih,decode_siteAct]
    rfl
lemma decode_rectangle (w h : ℕ) (f : FState) :
    decode (rectangleAct w h f)=gates physicalWeights (rectangleSites w h) (decode f) := by
  induction w generalizing f with
  | zero => rfl
  | succ w ih =>
    simp only [rectangleAct,rectangleSites,gates_append]
    rw [ih,decode_row]

/-- A literal prescribed spin word; the vacant positions are not summed. -/
noncomputable def stateOn : List Spin → FState
  | [] => emptyState
  | a::xs => consState (spinEquiv a) (stateOn xs)
lemma decode_stateOn (xs : List Spin) : decode (stateOn xs)=pointState xs := by
  induction xs with
  | nil => ext ys; cases ys <;> simp [decode,stateOn,emptyState,pointState]
  | cons a xs ih =>
    funext ys
    cases ys with
    | nil => simp [decode,stateOn,consState,pointState]
    | cons b ys =>
      change (if spinEquiv b=spinEquiv a then decode (stateOn xs) ys else 0)=_
      rw [ih]
      simp only [pointState,spinEquiv.injective.eq_iff,List.cons.injEq]
      by_cases h : b=a <;> simp [h]
lemma stateOn_vacuum (n : ℕ) : stateOn (List.replicate n none)=vacuum n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,stateOn,vacuum,ih]; rfl
lemma stateOn_prefix (n : ℕ) (xs : List Spin) :
    stateOn (List.replicate n none++xs)=prefixVac n (stateOn xs) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,List.cons_append,stateOn,prefixVac,ih]; rfl
lemma stateOn_source (pre post : ℕ) :
    stateOn (List.replicate pre none++some true::List.replicate post none)=sourceState pre post := by
  rw [stateOn_prefix]
  simp only [stateOn,stateOn_vacuum,sourceState]
  rfl

lemma physical_nonneg : 0≤kappa :=
  (Real.rpow_pos_of_pos (by positivity : (0:ℝ)<2+Real.sqrt 2) _).le
lemma physical_eq_realWeights : physicalWeights=realWeights kappa (kappa^2) (kappa^2) (kappa^2) 0 := by
  simp [physicalWeights,realWeights,Complex.ofReal_pow]

lemma rectangle_one_phase (w h : ℕ) (xs ys : List Spin) (hx : xs.length=w+h)
    (_hy : ys.length=w+h) {a : Bool} (hxs : orientations xs=[a])
    (hys : orientations ys=[a]) :
    PhasePositive (rectangleAct w h (stateOn xs) (ys.map spinEquiv)) 1 := by
  change PhasePositive (decode (rectangleAct w h (stateOn xs)) ys) 1
  rw [decode_rectangle,decode_stateOn,physical_eq_realWeights]
  have hs : PositiveSpan (w+h) 1 (fun zs=>if zs=[a] then 1 else 0) (pointState xs) := by
    simpa only [hx] using point_one_positive xs a hxs
  have hg := gates_positive physical_nonneg (sq_nonneg kappa) (sq_nonneg kappa)
    (sq_nonneg kappa) le_rfl (by omega : 1≤1) (rectangleSites w h)
    (rectangleSites_valid (N:=w+h) (by omega)) hs
  exact one_orientation_positive hg hys (by exact ⟨1,by positivity,by simp⟩)

lemma rectangle_input_pair_phase (w h : ℕ) (xs : List Spin) (hx : xs.length=w+h)
    {a b : Bool} (hxs : orientations xs=[a,b]) :
    PhasePositive (rectangleAct w h (stateOn xs) (List.replicate (w+h) 1)) (cup a b) := by
  have hv : (List.replicate (w+h) none).map spinEquiv=List.replicate (w+h) 1 := by simp [spinEquiv,PlanarNormalization.spinIndex]
  rw [←hv]
  change PhasePositive (decode (rectangleAct w h (stateOn xs)) (List.replicate (w+h) none)) _
  rw [decode_rectangle,decode_stateOn]
  rw [gates_kernel_transpose physicalWeights (rectangleSites w h)
    (rectangleSites_valid (by omega)) xs _ hx (by simp),physical_eq_realWeights]
  have hg := gates_positive physical_nonneg (sq_nonneg kappa) (sq_nonneg kappa)
    (sq_nonneg kappa) le_rfl (by omega : 0≤1) (rectangleSites w h).reverse
    (by intro i hi; exact rectangleSites_valid (N:=w+h) (by omega) i (List.mem_reverse.mp hi))
    (point_vacuum_positive (w+h))
  exact two_orientation_positive hg hxs

end Diagram
end CriticalHoneycomb.Transfer.FluxWard

namespace CriticalHoneycomb.Transfer.FluxWard
open scoped BigOperators
open PlanarNormalization

lemma r_pow_re (n : ℕ) : (r^n).re=Real.cos ((n:ℝ)*Real.pi/8) := by
  unfold r
  rw [←Complex.exp_nat_mul]
  have he : (n:ℂ)*(((Real.pi/8:ℝ):ℂ)*Complex.I)=
      (((n:ℝ)*Real.pi/8:ℝ):ℂ)*Complex.I := by push_cast;ring
  rw [he,Complex.exp_ofReal_mul_I_re]
lemma r_re_pos : 0<r.re := by
  have h := Real.pi_pos
  simpa using (show 0<(r^1).re from by rw [r_pow_re]; apply Real.cos_pos_of_mem_Ioo; constructor <;> linarith)
lemma r_re_le_one : r.re≤1 := by
  simpa using (show (r^1).re≤1 from by rw [r_pow_re]; exact Real.cos_le_one _)
lemma diagram_phase : PlanarNormalization.phase=r^2 := by
  rw [r_sq]
  unfold PlanarNormalization.phase Planar.phase Planar.angle
  congr 1
  push_cast
  ring
lemma before_coefficient_nonneg {q : ℂ} (hq : q=1 ∨ q=r) :
    0≤((-r^3)*q*PlanarNormalization.phase).re := by
  rw [diagram_phase]
  obtain rfl|rfl := hq
  · rw [show (-r^3)*(1:ℂ)*r^2= -r^5 by ring,Complex.neg_re,r_pow_re]
    have he : (5:ℝ)*Real.pi/8=Real.pi-3*Real.pi/8 := by ring
    norm_num only [Nat.cast_ofNat] at *
    rw [he,Real.cos_pi_sub,neg_neg]
    apply (Real.cos_pos_of_mem_Ioo _).le
    constructor <;> linarith [Real.pi_pos]
  · rw [show (-r^3)*r*r^2= -r^6 by ring,Complex.neg_re,r_pow_re]
    have he : (6:ℝ)*Real.pi/8=Real.pi-Real.pi/4 := by ring
    norm_num only [Nat.cast_ofNat] at *
    rw [he,Real.cos_pi_sub,neg_neg]
    apply (Real.cos_pos_of_mem_Ioo _).le
    constructor <;> linarith [Real.pi_pos]
lemma after_coefficient_nonneg {q : ℂ} (hq : q=1 ∨ q=r) :
    0≤(r^5*q*PlanarNormalization.phase⁻¹).re := by
  rw [diagram_phase]
  have hn : r≠0 := r_ne_zero
  obtain rfl|rfl := hq
  · rw [show r^5*(1:ℂ)*(r^2)⁻¹=r^3 from by field_simp [hn],r_pow_re]
    apply (Real.cos_pos_of_mem_Ioo _).le
    constructor <;> linarith [Real.pi_pos]
  · rw [show r^5*r*(r^2)⁻¹=r^4 from by field_simp [hn],r_pow_re]
    have he : (4:ℝ)*Real.pi/8=Real.pi/2 := by ring
    norm_num only [Nat.cast_ofNat]
    rw [he,Real.cos_pi_div_two]

lemma phasePositive_mul_real_nonneg {z p q : ℂ} (hz : PhasePositive z p)
    (hq : 0≤(q*p).re) : 0≤(q*z).re := by
  obtain ⟨a,ha,rfl⟩ := hz
  rw [show q*((a:ℂ)*p)=(a:ℂ)*(q*p) by ring]
  simpa using mul_nonneg ha hq

lemma prefixVac_zero (n : ℕ) : prefixVac n 0=0 := by
  have h := prefixVac_smul n 0 (0:FState)
  simpa using h
lemma rectangleAct_zero (w h : ℕ) : rectangleAct w h 0=0 := by
  have he := rectangleAct_smul w h 0 (0:FState)
  simpa using he

noncomputable def emptyEval (w h : ℕ) (f : FState) : ℂ :=
  rectangleAct w h f (List.replicate (w+h) 1)
lemma emptyEval_add (w h : ℕ) (f g : FState) :
    emptyEval w h (f+g)=emptyEval w h f+emptyEval w h g := by
  simp [emptyEval,rectangleAct_add]
lemma emptyEval_smul (w h : ℕ) (q : ℂ) (f : FState) :
    emptyEval w h (q • f)=q*emptyEval w h f := by
  simp [emptyEval,rectangleAct_smul]
lemma emptyEval_zero (w h : ℕ) : emptyEval w h 0=0 := by simp [emptyEval,rectangleAct_zero]

noncomputable def twoState (pre gap post : ℕ) (a b : Bool) : FState :=
  prefixVac pre (consState (Diagram.spinEquiv (some a))
    (prefixVac gap (consState (Diagram.spinEquiv (some b)) (vacuum post))))
lemma twoState_phase (w h pre gap post : ℕ) (a b : Bool)
    (hlen : pre+gap+post+2=w+h) :
    PhasePositive (emptyEval w h (twoState pre gap post a b)) (cup a b) := by
  let xs : List Diagram.Spin := List.replicate pre none++some a::
    (List.replicate gap none++some b::List.replicate post none)
  have hx : xs.length=w+h := by simp [xs];omega
  have he : Diagram.stateOn xs=twoState pre gap post a b := by
    simp only [xs,Diagram.stateOn_prefix,Diagram.stateOn,Diagram.stateOn_vacuum,twoState]
  rw [←he]
  exact Diagram.rectangle_input_pair_phase w h xs hx (by simp [xs,orientations])

lemma prefixVac_cons_one (n : ℕ) (f : FState) :
    prefixVac n (consState 1 f)=prefixVac (n+1) f := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [prefixVac] using congrArg (consState 1) ih

lemma before_real_nonneg (w h : ℕ) (pre : List ℂ) (post lead : ℕ)
    (hlen : lead+pre.length+1+post=w+h)
    (hpre : ∀ q∈pre,q=1 ∨ q=r) :
    0≤((-r^3)*emptyEval w h (prefixVac lead (beforeArches pre post))).re := by
  induction pre generalizing lead with
  | nil => simp [beforeArches,prefixVac_zero,emptyEval_zero]
  | cons q pre ih =>
    have hhead : 0≤((-r^3)*q*emptyEval w h
        (prefixVac lead (consState 0 (sourceState pre.length post)))).re := by
      apply phasePositive_mul_real_nonneg _ (before_coefficient_nonneg (hpre q (by simp)))
      change PhasePositive (emptyEval w h (twoState lead pre.length post false true)) (cup false true)
      exact twoState_phase w h lead pre.length post false true (by simp at hlen;omega)
    have htail := ih (lead+1) (by simp at hlen;omega) (by aesop)
    simp only [beforeArches,prefixVac_add,prefixVac_smul,emptyEval_add,emptyEval_smul]
    have he : prefixVac lead (consState 1 (beforeArches pre post))=
        prefixVac (lead+1) (beforeArches pre post) := by
      exact prefixVac_cons_one lead _
    rw [he,mul_add,Complex.add_re]
    simpa only [mul_assoc] using add_nonneg hhead htail

lemma after_real_nonneg (w h : ℕ) (post : List ℂ) (lead gap : ℕ)
    (hlen : lead+gap+1+post.length=w+h)
    (hpost : ∀ q∈post,q=1 ∨ q=r) :
    0≤(r^5*emptyEval w h
      (prefixVac lead (consState 2 (prefixVac gap (plusSum post))))).re := by
  induction post generalizing gap with
  | nil => simp [plusSum,prefixVac_zero,consState_zero,emptyEval_zero]
  | cons q post ih =>
    have hhead : 0≤(r^5*q*emptyEval w h (twoState lead gap post.length true false)).re := by
      apply phasePositive_mul_real_nonneg _ (after_coefficient_nonneg (hpost q (by simp)))
      exact twoState_phase w h lead gap post.length true false (by simp at hlen;omega)
    have htail := ih (gap+1) (by simp at hlen;omega) (by aesop)
    simp only [plusSum,prefixVac_smul,prefixVac_add,consState_add,consState_smul,
      emptyEval_add,emptyEval_smul]
    have he : prefixVac gap (consState 1 (plusSum post))=prefixVac (gap+1) (plusSum post) := by
      exact prefixVac_cons_one gap _
    rw [he,mul_add,Complex.add_re]
    change 0≤(r^5*(q*emptyEval w h (twoState lead gap post.length true false))).re+_
    exact add_nonneg (by simpa only [mul_assoc] using hhead) htail

end CriticalHoneycomb.Transfer.FluxWard

namespace CriticalHoneycomb.Transfer.FluxWard
open scoped BigOperators
open PlanarNormalization

def minusWord (pre post : ℕ) : List (Fin 3) :=
  List.replicate pre 1++2::List.replicate post 1

def OneNonneg (n : ℕ) (f : FState) : Prop :=
  ∀ pre post,pre+1+post=n → PhasePositive (f (minusWord pre post)) 1

lemma rectangle_source_positive (w h pre post : ℕ) (hlen : pre+1+post=w+h) :
    OneNonneg (w+h) (rectangleAct w h (sourceState pre post)) := by
  intro a b hab
  let xs : List Diagram.Spin := List.replicate pre none++some true::List.replicate post none
  let ys : List Diagram.Spin := List.replicate a none++some true::List.replicate b none
  have hx : xs.length=w+h := by simp [xs];omega
  have hy : ys.length=w+h := by simp [ys];omega
  have hs : Diagram.stateOn xs=sourceState pre post := Diagram.stateOn_source pre post
  have ht : ys.map Diagram.spinEquiv=minusWord a b := by
    simp [ys,minusWord,Diagram.spinEquiv,spinIndex]
  rw [←hs,←ht]
  exact Diagram.rectangle_one_phase w h xs ys hx hy (a:=true) (by simp [xs,orientations])
    (by simp [ys,orientations])

lemma exitSum_real_nonneg (qs : List ℂ) (f : FState)
    (hf : OneNonneg qs.length f) (hq : ∀ q∈qs,0≤q.re) :
    0≤(exitSum qs f).re := by
  induction qs generalizing f with
  | nil => simp [exitSum]
  | cons q qs ih =>
    rw [exitSum,Complex.add_re]
    apply add_nonneg
    · apply phasePositive_mul_real_nonneg (hf 0 qs.length (by simp;omega))
      simpa using hq q (by simp)
    · apply ih
      · intro a b hab
        simpa [minusWord,List.replicate_succ] using hf (a+1) b (by simp;omega)
      · intro u hu;exact hq u (by simp [hu])

lemma exitSum_append (as bs : List ℂ) (f : FState) :
    exitSum (as++bs) f =
      exitSum as (fun xs=>f (xs++List.replicate bs.length 1)) +
      exitSum bs (fun xs=>f (List.replicate as.length 1++xs)) := by
  induction as generalizing f with
  | nil => simp [exitSum]
  | cons a as ih =>
    simp only [List.cons_append,exitSum,List.length_append,List.length_cons]
    rw [ih]
    simp only [List.replicate_add,List.cons_append,List.replicate_succ]
    ring

lemma rectangle_output_bound (w h : ℕ) (pre post : List ℂ) (q : ℂ)
    (directions : List.replicate w r++List.replicate h 1=pre++q::post) :
    (exitSum (List.replicate h 1++List.replicate w r)
      (rectangleAct w h (sourceState pre.length post.length))).re≤q.re := by
  have len : pre.length+1+post.length=w+h := by
    have he := congrArg List.length directions
    simp only [List.length_append,List.length_replicate,List.length_cons] at he
    omega
  have hd : ∀ z∈pre++q::post,z=1 ∨ z=r := by
    rw [←directions]
    intro z hz
    simp only [List.mem_append,List.mem_replicate] at hz
    aesop
  have hb := before_real_nonneg w h pre post.length 0 (by omega)
    (by intro z hz;exact hd z (List.mem_append_left _ hz))
  have ha := after_real_nonneg w h post pre.length 0 (by omega)
    (by intro z hz;exact hd z (List.mem_append_right _ (List.mem_cons_of_mem _ hz)))
  simp only [prefixVac] at hb ha
  have he := rectangle_boundary_flux w h pre post q directions
  rw [rectangle_vacuum_one,show h+w=w+h by omega] at he
  have hre := congrArg Complex.re he
  simp only [Complex.add_re,mul_one] at hre
  change (exitSum _ _).re+((-r^3)*emptyEval w h (beforeArches pre post.length)).re+
    (r^5*emptyEval w h (afterArches pre.length post)).re=q.re at hre
  change 0≤(r^5*emptyEval w h (afterArches pre.length post)).re at ha
  linarith

/-- Finite physical parafermionic flux bounds the total opposite-side
one-strand coefficient, uniformly in both rectangle dimensions. -/
theorem rectangle_west_exit_bound (w k post : ℕ) :
    (exitSum (List.replicate (k+1+post) 1)
      (fun xs=>rectangleAct w (k+1+post) (sourceState (w+k) post)
        (xs++List.replicate w 1))).re≤1 := by
  let h := k+1+post
  have hd : List.replicate w r++List.replicate h (1:ℂ)=
      (List.replicate w r++List.replicate k 1)++1::List.replicate post 1 := by
    change List.replicate w r++List.replicate (k+1+post) (1:ℂ)=_
    rw [show k+1+post=k+(1+post) by omega,List.replicate_add]
    simp only [show 1+post=post+1 by omega,List.replicate_succ,List.append_assoc]
  have he := rectangle_output_bound w h (List.replicate w r++List.replicate k 1)
    (List.replicate post 1) 1 hd
  simp only [List.length_append,List.length_replicate,Complex.one_re] at he
  rw [exitSum_append,Complex.add_re] at he
  have hn : 0≤(exitSum (List.replicate w r)
      (fun xs=>rectangleAct w h (sourceState (w+k) post)
        (List.replicate h 1++xs))).re := by
    apply exitSum_real_nonneg
    · intro a b hab
      have hp := rectangle_source_positive w h (w+k) post (by dsimp [h];omega)
      simpa only [minusWord,List.replicate_add,List.append_assoc] using hp (h+a) b (by simp at hab;omega)
    · intro q hq
      obtain ⟨_,rfl⟩ := List.mem_replicate.mp hq
      exact r_re_pos.le
  simp only [List.length_replicate] at he
  dsimp [h] at he hn
  linarith

end CriticalHoneycomb.Transfer.FluxWard

namespace CriticalHoneycomb.Transfer.FluxWard
open scoped BigOperators Matrix

lemma siteAct_zero_state (i : ℕ) : siteAct i 0=0 := by
  have h := siteAct_smul i 0 (0:FState)
  simpa using h

lemma siteAct_congr_length (i n : ℕ) (f g : FState)
    (hfg : ∀ xs,xs.length=n → f xs=g xs) :
    ∀ xs,xs.length=n → siteAct i f xs=siteAct i g xs := by
  induction i generalizing n f g with
  | zero =>
    intro xs hx
    cases xs with
    | nil => rfl
    | cons a xs => cases xs with
      | nil => rfl
      | cons b xs =>
        simp only [siteAct]
        apply Finset.sum_congr rfl
        intro c hc
        apply Finset.sum_congr rfl
        intro d hd
        rw [hfg (c::d::xs) (by simpa using hx)]
  | succ i ih =>
    intro xs hx
    cases xs with
    | nil => rfl
    | cons a xs =>
      simp only [siteAct]
      apply ih (n-1)
      · intro ys hy;apply hfg; simp at hx ⊢; omega
      · simp at hx;omega

lemma rowAct_congr_length (i h n : ℕ) (f g : FState)
    (hfg : ∀ xs,xs.length=n → f xs=g xs) :
    ∀ xs,xs.length=n → rowAct i h f xs=rowAct i h g xs := by
  induction h generalizing i f g with
  | zero => exact hfg
  | succ h ih => exact ih (i+1) _ _ (siteAct_congr_length i n f g hfg)

lemma rectangleAct_congr_length (w h n : ℕ) (f g : FState)
    (hfg : ∀ xs,xs.length=n → f xs=g xs) :
    ∀ xs,xs.length=n → rectangleAct w h f xs=rectangleAct w h g xs := by
  induction w generalizing f g with
  | zero => exact hfg
  | succ w ih => exact ih _ _ (rowAct_congr_length w h n f g hfg)

lemma siteAct_suffix (i : ℕ) (f : FState) (xs ys : List (Fin 3))
    (hi : i+2≤xs.length) :
    siteAct i f (xs++ys)=siteAct i (fun zs=>f (zs++ys)) xs := by
  induction i generalizing f xs with
  | zero =>
    cases xs with
    | nil => simp at hi
    | cons a xs => cases xs with
      | nil => simp at hi
      | cons b xs => rfl
  | succ i ih =>
    cases xs with
    | nil => simp at hi
    | cons a xs =>
      simpa only [List.cons_append,siteAct] using
        ih (fun zs=>f (a::zs)) xs (by simp at hi;omega)

lemma rowAct_suffix (i h : ℕ) (f : FState) (xs ys : List (Fin 3))
    (hi : i+h<xs.length) :
    rowAct i h f (xs++ys)=rowAct i h (fun zs=>f (zs++ys)) xs := by
  induction h generalizing i f with
  | zero => rfl
  | succ h ih =>
    simp only [rowAct]
    rw [ih (i+1) (siteAct i f) (by omega)]
    apply rowAct_congr_length (i+1) h xs.length _ _ _ xs rfl
    intro zs hz
    exact siteAct_suffix i f zs ys (by omega)

lemma rectangleAct_suffix (w h : ℕ) (f : FState) (xs ys : List (Fin 3))
    (hi : w+h≤xs.length) :
    rectangleAct w h f (xs++ys)=rectangleAct w h (fun zs=>f (zs++ys)) xs := by
  induction w generalizing f with
  | zero => rfl
  | succ w ih =>
    simp only [rectangleAct]
    rw [ih (rowAct w h f) (by omega)]
    apply rectangleAct_congr_length w h xs.length _ _ _ xs rfl
    intro zs hz
    exact rowAct_suffix w h f zs ys (by omega)

lemma siteAct_prefixVac (pre i : ℕ) (f : FState) :
    siteAct (pre+i) (prefixVac pre f)=prefixVac pre (siteAct i f) := by
  induction pre generalizing f with
  | zero => simp only [Nat.zero_add,prefixVac]
  | succ pre ih =>
    rw [show pre+1+i=(pre+i)+1 by omega]
    funext xs
    cases xs with
    | nil => rfl
    | cons a xs =>
      simp only [prefixVac,siteAct,consState]
      by_cases ha : a=1
      · simp only [ha,ite_true]
        exact congrFun (ih f) xs
      · simp only [ha,ite_false]
        change siteAct (pre+i) (0:FState) xs=0
        rw [siteAct_zero_state]
        rfl

lemma rowAct_prefixVac (pre i h : ℕ) (f : FState) :
    rowAct (pre+i) h (prefixVac pre f)=prefixVac pre (rowAct i h f) := by
  induction h generalizing i f with
  | zero => rfl
  | succ h ih =>
    simp only [rowAct,siteAct_prefixVac]
    rw [show pre+i+1=pre+(i+1) by omega,ih]

lemma prefixVac_eval_append (pre : ℕ) (f : FState) (xs ys : List (Fin 3))
    (hx : pre≤xs.length) :
    prefixVac pre f (xs++ys)=prefixVac pre (fun zs=>f (zs++ys)) xs := by
  induction pre generalizing xs with
  | zero => rfl
  | succ pre ih =>
    cases xs with
    | nil => simp at hx
    | cons a xs =>
      simp only [List.cons_append,prefixVac,consState]
      split_ifs
      · exact ih xs (by simp at hx;omega)
      · rfl

noncomputable def vacuumColumn (h : ℕ) (f : FState) : FState :=
  fun xs=>rowAct 0 h (consState 1 f) (xs++[1])

/-- Sweeping the lozenge rectangle and then fixing the north boundary
is exactly iteration of its literal empty-auxiliary column. -/
theorem rectangle_eq_columns (w h : ℕ) (f : FState) (xs : List (Fin 3))
    (hx : xs.length=h) :
    rectangleAct w h (prefixVac w f) (xs++List.replicate w 1)=
      (vacuumColumn h)^[w] f xs := by
  induction w generalizing f with
  | zero => simp [rectangleAct,prefixVac]
  | succ w ih =>
    have hp : prefixVac (w+1) f=prefixVac w (consState 1 f) := by
      exact (prefixVac_cons_one w f).symm
    rw [rectangleAct,hp]
    have hr := rowAct_prefixVac w 0 h (consState 1 f)
    simp only [Nat.add_zero] at hr
    rw [hr]
    rw [show List.replicate (w+1) (1:Fin 3)=List.replicate w 1++[1] by
      rw [List.replicate_add];rfl,←List.append_assoc]
    rw [rectangleAct_suffix w h _ _ _ (by simp [hx];omega)]
    have he : ∀ zs,zs.length=w+h →
        prefixVac w (rowAct 0 h (consState 1 f)) (zs++[1])=
          prefixVac w (vacuumColumn h f) zs := by
      intro zs hz
      exact prefixVac_eval_append w _ zs [1] (by omega)
    rw [rectangleAct_congr_length w h (w+h) _ _ he _ (by simp [hx];omega),ih]
    rw [Function.iterate_succ_apply]

end CriticalHoneycomb.Transfer.FluxWard

namespace CriticalHoneycomb.Transfer.FluxWard
open scoped BigOperators Matrix

lemma decode_rowAct (i h : ℕ) (f : FState) :
    Diagram.decode (rowAct i h f)=
      PlanarNormalization.planarRow i (List.replicate h Diagram.physicalWeights) (Diagram.decode f) := by
  induction h generalizing i f with
  | zero => rfl
  | succ h ih =>
    simp only [rowAct,List.replicate_succ,PlanarNormalization.planarRow,ih,Diagram.decode_siteAct]

lemma spinEquiv_eq : Diagram.spinEquiv=RasterGrid.spinEquiv := rfl
lemma physicalWeights_eq : Diagram.physicalWeights=RasterGrid.physicalWeights := rfl

noncomputable def columnBasis {h : ℕ} (east : RasterGrid.Column h) : FState :=
  fun xs=>if xs=List.ofFn east then 1 else 0

lemma cons_columnBasis {h : ℕ} (east : RasterGrid.Column h) :
    consState 1 (columnBasis east)=fun xs=>if xs=1::List.ofFn east then 1 else 0 := by
  funext xs
  cases xs with
  | nil => simp [consState]
  | cons a xs =>
    by_cases ha : a=1 <;> by_cases hx : xs=List.ofFn east <;>
      simp [consState,columnBasis,ha,hx]

lemma vacuumColumn_basis_eq_kernel (h : ℕ) (west east : RasterGrid.Column h) :
    vacuumColumn h (columnBasis east) (List.ofFn west)=
      RasterGrid.columnKernel h 1 1 west east := by
  let we := (RasterGrid.columnSpinEquiv h).symm west
  let ea := (RasterGrid.columnSpinEquiv h).symm east
  have hw : RasterGrid.columnSpinEquiv h we=west := (RasterGrid.columnSpinEquiv h).apply_symm_apply west
  have he : RasterGrid.columnSpinEquiv h ea=east := (RasterGrid.columnSpinEquiv h).apply_symm_apply east
  rw [←hw,←he]
  have hk := RasterGrid.columnKernel_eq_planarRow h none none we ea
  change RasterGrid.columnKernel h 1 1 _ _ = _ at hk
  rw [hk]
  change vacuumColumn h (columnBasis _) (List.ofFn _)=_
  have hl : List.ofFn (RasterGrid.columnSpinEquiv h we)++[1]=
      (List.ofFn we++[none]).map Diagram.spinEquiv := by
    simp [RasterGrid.columnSpinEquiv,List.map_ofFn,Diagram.spinEquiv,PlanarNormalization.spinIndex]
    rfl
  unfold vacuumColumn
  rw [hl]
  change Diagram.decode (rowAct 0 h (consState 1 (columnBasis _))) (List.ofFn we++[none])=_
  rw [decode_rowAct,physicalWeights_eq,cons_columnBasis]
  congr 2
  funext xs
  unfold Diagram.decode
  have hmap : Diagram.spinEquiv <$> (none::List.ofFn ea)=1::List.ofFn (RasterGrid.columnSpinEquiv h ea) := by
    simp [RasterGrid.columnSpinEquiv,List.map_ofFn,Diagram.spinEquiv,PlanarNormalization.spinIndex]
    rfl
  rw [←hmap]
  change (if xs.map Diagram.spinEquiv = (none::List.ofFn ea).map Diagram.spinEquiv then 1 else 0)=_
  simp only [List.map_inj_right (fun _ _ h=>Diagram.spinEquiv.injective h)]

end CriticalHoneycomb.Transfer.FluxWard

namespace CriticalHoneycomb.Transfer.FluxWard
open scoped BigOperators Matrix

lemma consState_sum {α : Type*} [Fintype α] (b : Fin 3) (f : α → FState) :
    consState b (fun xs=>∑ a,f a xs)=fun xs=>∑ a,consState b (f a) xs := by
  funext xs
  cases xs <;> simp [consState] 

lemma rowAct_sum {α : Type*} [Fintype α] (i h : ℕ) (f : α → FState) :
    rowAct i h (fun xs=>∑ a,f a xs)=fun xs=>∑ a,rowAct i h (f a) xs := by
  induction h generalizing i f with
  | zero => rfl
  | succ h ih =>
    simp only [rowAct]
    rw [show siteAct i (fun xs=>∑ a,f a xs)=fun xs=>∑ a,siteAct i (f a) xs from by
      funext xs; exact siteAct_sum i f xs,ih]

lemma vacuumColumn_sum {α : Type*} [Fintype α] (h : ℕ) (f : α → FState) :
    vacuumColumn h (fun xs=>∑ a,f a xs)=fun xs=>∑ a,vacuumColumn h (f a) xs := by
  funext xs
  simp only [vacuumColumn,consState_sum,rowAct_sum]
lemma vacuumColumn_scalar (h : ℕ) (z : ℂ) (f : FState) :
    vacuumColumn h (fun xs=>z*f xs)=fun xs=>z*vacuumColumn h f xs := by
  funext xs
  change vacuumColumn h (z • f) xs=_
  simp only [vacuumColumn,consState_smul,rowAct_smul,Pi.smul_apply,smul_eq_mul]

lemma columnBasis_expansion (h : ℕ) (f : FState) (xs : List (Fin 3)) (hx : xs.length=h) :
    f xs=∑ east : RasterGrid.Column h,f (List.ofFn east)*columnBasis east xs := by
  classical
  subst h
  have he : List.ofFn xs.get=xs := List.ofFn_get xs
  have hb (east : RasterGrid.Column xs.length) : xs=List.ofFn east ↔ xs.get=east := by
    calc
      xs=List.ofFn east ↔ List.ofFn xs.get=List.ofFn east := by rw [List.ofFn_get]
      _ ↔ xs.get=east := List.ofFn_inj
  simp [columnBasis,hb,mul_ite,he]

lemma vacuumColumn_congr (h : ℕ) (f g : FState)
    (hfg : ∀ xs,xs.length=h → f xs=g xs) (xs : List (Fin 3)) (hx : xs.length=h) :
    vacuumColumn h f xs=vacuumColumn h g xs := by
  apply rowAct_congr_length 0 h (h+1) _ _ _ _ (by simp [hx])
  intro ys hy
  cases ys with
  | nil => simp at hy
  | cons a ys =>
    by_cases ha : a=1
    · simp only [consState,ha,ite_true]
      exact hfg ys (by simpa using hy)
    · simp [consState,ha]

lemma vacuumColumn_as_matrix (h : ℕ) (f : FState) (west : RasterGrid.Column h) :
    vacuumColumn h f (List.ofFn west)=
      ∑ east : RasterGrid.Column h,RasterGrid.columnKernel h 1 1 west east*f (List.ofFn east) := by
  rw [vacuumColumn_congr h f (fun xs=>∑ east : RasterGrid.Column h,
      f (List.ofFn east)*columnBasis east xs) (columnBasis_expansion h f) _ (List.length_ofFn),
    vacuumColumn_sum]
  apply Finset.sum_congr rfl
  intro east he
  rw [vacuumColumn_scalar]
  change f (List.ofFn east)*vacuumColumn h (columnBasis east) (List.ofFn west)=_
  rw [vacuumColumn_basis_eq_kernel,mul_comm]

lemma iterateColumn_basis_eq_power (w h : ℕ) (west east : RasterGrid.Column h) :
    (vacuumColumn h)^[w] (columnBasis east) (List.ofFn west)=
      ((RasterGrid.columnKernel h 1 1)^w) west east := by
  induction w generalizing west with
  | zero => simp [columnBasis,Matrix.one_apply,List.ofFn_inj]
  | succ w ih =>
    rw [Function.iterate_succ_apply',vacuumColumn_as_matrix,pow_succ',Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro middle hm
    rw [ih]

/-- Literal finite rectangle: the flux raster and the actual center/path
matrix use exactly the same vacuum north/south boundary and ordering. -/
theorem rectangle_columnBasis_eq_prescribed (w h : ℕ) (west east : RasterGrid.Column h) :
    rectangleAct w h (prefixVac w (columnBasis east))
      (List.ofFn west++List.replicate w 1)=
      RasterGrid.prescribedPartition w h west east (fun _=>1) (fun _=>1) := by
  rw [rectangle_eq_columns w h _ _ (List.length_ofFn),iterateColumn_basis_eq_power,
    RasterGrid.prescribedPartition_eq_transfer]
  simp

end CriticalHoneycomb.Transfer.FluxWard

namespace CriticalHoneycomb.Transfer.FluxWard
open scoped BigOperators
lemma vacuum_indicator (n : ℕ) (xs : List (Fin 3)) :
    vacuum n xs=if xs=List.replicate n 1 then 1 else 0 := by
  induction n generalizing xs with
  | zero => cases xs <;> simp [vacuum,emptyState]
  | succ n ih =>
    cases xs with
    | nil => simp [vacuum,consState]
    | cons a xs =>
      by_cases ha : a=1 <;> simp [vacuum,consState,ha,ih,List.replicate_succ]

lemma prefixVac_indicator (n : ℕ) (ys : List (Fin 3)) :
    prefixVac n (fun xs=>if xs=ys then 1 else 0)=
      fun xs=>if xs=List.replicate n 1++ys then 1 else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext xs
    cases xs with
    | nil => simp [prefixVac,consState]
    | cons a xs =>
      by_cases ha : a=1 <;> simp [prefixVac,consState,ha,ih,List.replicate_succ]

lemma sourceState_indicator (pre post : ℕ) :
    sourceState pre post =
      fun xs=>if xs=List.replicate pre 1++2::List.replicate post 1 then 1 else 0 := by
  have hv : vacuum post=fun xs=>if xs=List.replicate post 1 then 1 else 0 :=
    funext (vacuum_indicator post)
  unfold sourceState
  rw [hv]
  have hc : consState 2 (fun xs=>if xs=List.replicate post 1 then 1 else 0)=
      fun xs=>if xs=2::List.replicate post 1 then 1 else 0 := by
    funext xs
    cases xs with
    | nil => simp [consState]
    | cons a xs => by_cases ha : a=2 <;> simp [consState,ha]
  rw [hc,prefixVac_indicator]

lemma singleColumn_list {h : ℕ} (j : Fin h) :
    List.ofFn (RasterGrid.singleColumn j)=
      List.replicate j.val 1++2::List.replicate (h-1-j.val) 1 := by
  apply List.ext_getElem
  · simp
    omega
  · intro n h₁ h₂
    have hnH : n<h := by simpa using h₁
    simp only [List.getElem_ofFn,RasterGrid.singleColumn]
    by_cases hn : n<j.val
    · rw [List.getElem_append_left (by simpa using hn)]
      simp only [List.getElem_replicate]
      have hne : (⟨n,hnH⟩:Fin h)≠j := by intro hh;have hh : n=j.val := congrArg Fin.val hh;omega
      simp [hne]
    · rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt hn)]
      by_cases he : n=j.val
      · subst n
        simp
      · have hh : j.val<n := by omega
        have hne : (⟨n,hnH⟩:Fin h)≠j := by intro hh;exact he (congrArg Fin.val hh)
        simp only [ite_eq_right hne,List.length_replicate]
        rw [List.getElem_cons]
        simp [show n-j.val≠0 by omega]

lemma sourceState_eq_basis (h : ℕ) (j : Fin h) :
    sourceState j.val (h-1-j.val)=columnBasis (RasterGrid.singleColumn j) := by
  rw [sourceState_indicator]
  unfold columnBasis
  rw [singleColumn_list]

lemma prefixVac_source (w pre post : ℕ) :
    prefixVac w (sourceState pre post)=sourceState (w+pre) post := by
  induction w with
  | zero => simp [prefixVac]
  | succ w ih => simpa [sourceState,prefixVac,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using congrArg (consState 1) ih

lemma exitSum_eq_sum (h : ℕ) (f : FState) :
    exitSum (List.replicate h 1) f=∑ j : Fin h,f (List.ofFn (RasterGrid.singleColumn j)) := by
  induction h generalizing f with
  | zero => simp [exitSum]
  | succ h ih =>
    rw [List.replicate_succ,exitSum,ih,Fin.sum_univ_succ]
    simp only [List.length_replicate,one_mul]
    congr 1
    · congr 1
      rw [singleColumn_list]
      simp
    · apply Finset.sum_congr rfl
      intro j hj
      congr 1
      rw [singleColumn_list,singleColumn_list]
      simp only [Fin.val_succ,List.replicate_succ,List.cons_append]
      rw [show h-1-j.val=(h+1)-1-(j.val+1) by omega]

/-- The actual literal honeycomb chord sum to the opposite wall, not an
abstract positivity assumption on a transfer matrix. -/
theorem rectangle_actual_sum_bound (W H : ℕ) (k : Fin (H+1)) :
    (∑ j : Fin (H+1),∑ γ : RasterGrid.RectChord W H j k,
      kappa^γ.val.length)≤1 := by
  classical
  have hf := rectangle_west_exit_bound (W+1) k.val (H-k.val)
  have hk := k.isLt
  have hl : k.val+1+(H-k.val)=H+1 := by omega
  rw [hl] at hf
  have hs : sourceState (W+1+k.val) (H-k.val)=
      prefixVac (W+1) (columnBasis (RasterGrid.singleColumn k)) := by
    rw [←sourceState_eq_basis,prefixVac_source]
    simp
  rw [hs,exitSum_eq_sum] at hf
  simpa only [rectangle_columnBasis_eq_prescribed,RasterGrid.actual_chord_sum_eq_transfer,
    Complex.re_sum,←Complex.ofReal_pow,Complex.ofReal_re] using hf

theorem rectangle_actual_mass_bound (W H : ℕ) (k : Fin (H+1)) :
    (∑ j : Fin (H+1),chordMass (RasterGrid.domain (W+1) (H+1) : Set Center)
      (RasterGrid.westPort W H j) (RasterGrid.eastPort W H k))≤1 := by
  classical
  simp_rw [RasterGrid.actual_chordMass_eq_transfer,RasterGrid.actual_chord_sum_eq_transfer,
    Complex.re_sum,←Complex.ofReal_pow,Complex.ofReal_re]
  rw [←ENNReal.ofReal_sum_of_nonneg]
  · exact (ENNReal.ofReal_le_ofReal (rectangle_actual_sum_bound W H k)).trans (by simp)
  · intro j hj
    apply Finset.sum_nonneg
    intro γ hγ
    apply pow_nonneg
    exact (Real.rpow_pos_of_pos (by positivity : (0:ℝ)<2+Real.sqrt 2) _).le
end CriticalHoneycomb.Transfer.FluxWard


end OAI
