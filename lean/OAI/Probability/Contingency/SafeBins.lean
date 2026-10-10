import Mathlib
import OAI.Probability.Contingency.GridCover

namespace OAI

/-! Safe Bins. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
namespace Contingency.Grid
noncomputable section
variable {q K : ℕ} {I : Type*}
open Contingency.Interpolation Contingency.Dense

def closedBin (v : Vertex q K) : Set (Fin q → ℝ) :=
  Set.pi Set.univ (fun i => Set.Icc (v i:ℝ) ((v i:ℝ)+1))

def safeBins (f : I → (Fin q → ℝ) → ℝ) : Finset (Vertex q K) := by
  classical
  exact Finset.univ.filter fun v => closedBin v ⊆ region f 0

@[simp] theorem mem_safeBins (f : I → (Fin q → ℝ) → ℝ) (v : Vertex q K) :
    v∈safeBins f ↔ closedBin v ⊆ region f 0 := by classical simp [safeBins]

theorem closedBin_distance (v : Vertex q K) (x y : Fin q → ℝ)
    (hx : x∈(bin v).carrier) (hy : y∈closedBin v) : ‖y-x‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
  intro i
  have h1 := (mem_bin v x).mp hx i
  have h2 := hy i (Set.mem_univ i)
  dsimp [inside,corner] at h1
  simp only [Set.mem_Icc] at h2
  simp only [Pi.sub_apply,Real.norm_eq_abs,abs_le]
  constructor <;> linarith [h1.1,h1.2,h2.1,h2.2]

theorem inner_bin_safe (f : I → (Fin q → ℝ) → ℝ) (L τ : ℝ)
    (hL : 0 ≤ L) (hτ : L ≤ τ) (hlip : ∀ i x y,|f i x-f i y| ≤ L*‖x-y‖)
    (v : Vertex q K) (x : Fin q → ℝ) (hx : x∈region f τ) (hbin : x∈(bin v).carrier) :
    v∈safeBins f := by
  rw [mem_safeBins]
  intro y hy i
  have hh := (hlip i y x).trans (mul_le_mul_of_nonneg_left (closedBin_distance v x y hbin hy) hL)
  have hi := hx i
  rw [mul_one] at hh
  linarith only [(abs_le.mp hh).1,hi,hτ]

theorem boxes_volume_le_card (V : Finset (Vertex q K)) :
    volume (boxUnion (boxes V)) ≤ V.card := by
  have he : boxUnion (boxes V)=⋃ v∈V,(bin v).carrier := by
    ext x
    simp only [mem_boxes,mem_iUnion,mem_bin,exists_prop]
  rw [he]
  apply (measure_biUnion_finset_le V (fun v => (bin v).carrier)).trans_eq
  simp [bin_volume]

theorem safe_bin_count (f : I → (Fin q → ℝ) → ℝ) (L τ bound : ℝ)
    (hL : 0 ≤ L) (hτ : L ≤ τ) (hlip : ∀ i x y,|f i x-f i y| ≤ L*‖x-y‖)
    (hbound : region f 0 ⊆ Set.pi Set.univ (fun _ => Set.Icc 0 bound))
    (hK : bound < K) : volume (region f τ) ≤ (safeBins (K:=K) f).card := by
  apply le_trans _ (boxes_volume_le_card (safeBins f))
  apply measure_mono_ae
  filter_upwards [ae_no_grid (q:=q)] with x hgrid
  intro hx
  have hx0 : x∈region f 0 := fun i => (hL.trans hτ).trans (hx i)
  have hxcube : x∈(cube q K).carrier := by
    rw [mem_cube]
    intro i
    have hh := hbound hx0 i (Set.mem_univ i)
    exact ⟨lt_of_le_of_ne hh.1 (Ne.symm (by simpa only [Nat.cast_zero] using hgrid i 0)),hh.2.trans_lt hK⟩
  obtain ⟨v,hv⟩ := exists_bin x hxcube hgrid
  exact (mem_boxes _ _).mpr ⟨v,inner_bin_safe f L τ hL hτ hlip v x hx ((mem_bin v x).mpr hv),hv⟩

theorem corner_mem_closedBin (v : Vertex q K) : realCorner v∈closedBin v := by
  intro i _
  exact ⟨le_rfl,by dsimp [realCorner]; linarith⟩

theorem safe_bin_weight_one {a c : ℕ} (e : Fin q ≃ Fin a×Fin c)
    (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ) (w : Fin a → Fin c → ℝ)
    (d : ℝ) (hd : 0 ≤ d) (v : Vertex q K)
    (hv : v∈safeBins (constraints e R P w)) : binWeight e R P w d v=1 := by
  have hs := (mem_safeBins _ v).mp hv (corner_mem_closedBin v)
  have hz : penalty R P w (d^8) d (fun s => realCorner v (e.symm s))=0 := by
    apply penalty_zero_of_slack
    intro i j
    have hh := hs (i,j)
    have hn : 0 ≤ d/d^8 := by positivity
    change 0 ≤ normalized R P w _ i j at hh
    rw [neg_div]
    linarith
  simp [binWeight,exponentWeight,binExponent,hz]

end
end Contingency.Grid

 

 

open Set MeasureTheory
open scoped BigOperators
namespace Contingency.Dense
noncomputable section
variable {a c q K : ℕ}
open Contingency.Grid Contingency.Interpolation

 

theorem dense_safe_bin_bound (e : Fin q ≃ Fin a×Fin c)
    (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ) (w : Fin a → Fin c → ℝ)
    (d : ℝ) (hd : 4 ≤ d) (hq : (q:ℝ) ≤ d)
    (ha : (a+1:ℕ) ≤ d) (hc : (c+1:ℕ) ≤ d) (hK : 2*d^8 < K)
    (hR : ∀ i,0<R i) (hP : ∀ j,0<P j) (heq : (∑ i,R i)=∑ j,P j)
    (hRmax : ∀ i,R i ≤ R (Fin.last a)) (hPmax : ∀ j,P j ≤ P (Fin.last c))
    (hwlo : ∀ i j,scale R P i.castSucc j.castSucc/(2*d^8) ≤ w i j)
    (hwhi : ∀ i j,w i j ≤ scale R P i.castSucc j.castSucc/d^8) :
    (∑ v : Vertex q K,binWeight e R P w d v)/32 ≤ ((safeBins (K:=K) (constraints e R P w)).card:ℝ) := by
  have hd0 : 0<d := by linarith
  have hw (i j) : 0<w i j :=
    (div_pos (lt_min (hR _) (hP _)) (by positivity)).trans_le (hwlo i j)
  have hcard : q=a*c := by simpa using Fintype.card_congr e
  have he : (a*c:ℕ) ≤ d := by rw [← hcard]; exact hq
  obtain ⟨u,hu⟩ := region_interior e d hd0 R P w hR hP heq ha hc hw
  have hinner := inner_half_volume (constraints e R P w) (constraints_affine e R P w) d (by linarith) hq u hu
  have hlip := fun i x y => constraints_lipschitz e R P w (d^8) d (by positivity) hd0.le he
    hR hP hRmax hPmax (fun i j => (hw i j).le) hwhi x y i
  have hcubes := region_bounded e R P w (d^8) (by positivity) hR hP heq hwlo
  have hcount := safe_bin_count (K:=K) (constraints e R P w) (d/d^8) (2*d/d^8) (2*d^8)
    (by positivity) (div_le_div_of_nonneg_right (by linarith : d ≤ 2*d) (by positivity)) hlip hcubes hK
  have hlow := hinner.trans hcount
  have hnorm := dense_bin_normalizer_bound (K:=K) e R P w d hd he hq hR hP hRmax hPmax
    (fun i j => (hw i j).le) hwhi u hu
  have hcoef : (32:ENNReal)*(1/2)=16 := by
    have h : (32:NNReal)*(1/2)=16 := by norm_num
    have hh := congrArg (fun x : NNReal => (x:ENNReal)) h
    simpa only [ENNReal.coe_mul,ENNReal.coe_div (by norm_num : (2:NNReal)≠0),ENNReal.coe_one,ENNReal.coe_ofNat] using hh
  have hupper : ENNReal.ofReal (∑ v : Vertex q K,binWeight e R P w d v) ≤
      32*((safeBins (K:=K) (constraints e R P w)).card:ENNReal) := by
    calc
      _ ≤ 16*volume (region (constraints e R P w) 0) := hnorm
      _ = 32*((1/2:ENNReal)*volume (region (constraints e R P w) 0)) := by rw [← mul_assoc,hcoef]
      _ ≤ _ := by gcongr
  have he' : ENNReal.ofReal (32*((safeBins (K:=K) (constraints e R P w)).card:ℝ)) =
      32*((safeBins (K:=K) (constraints e R P w)).card:ENNReal) := by
    rw [ENNReal.ofReal_mul (by norm_num),ENNReal.ofReal_natCast]
    norm_num
  rw [← he'] at hupper
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 32*((safeBins (K:=K) (constraints e R P w)).card:ℝ))).mp hupper
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<32)).mpr
  simpa only [mul_comm] using hreal

end
end Contingency.Dense

 

 

open scoped BigOperators
namespace Contingency.Dense
noncomputable section
open Contingency.Grid
variable {a c q K : ℕ}

 
def integerComplete (R : Fin (a+1) → ℕ) (P : Fin (c+1) → ℕ)
    (x : Fin a → Fin c → ℕ) : Fin (a+1) → Fin (c+1) → ℤ :=
  Fin.lastCases
    (Fin.lastCases ((R (Fin.last a):ℤ)-(∑ j : Fin c,(P j.castSucc:ℤ))+(∑ i,∑ j,(x i j:ℤ)))
      (fun j => (P j.castSucc:ℤ)-∑ i,(x i j:ℤ)))
    (fun i => Fin.lastCases ((R i.castSucc:ℤ)-∑ j,(x i j:ℤ)) (fun j => (x i j:ℤ)))

theorem integerComplete_cast (R : Fin (a+1) → ℕ) (P : Fin (c+1) → ℕ)
    (x : Fin a → Fin c → ℕ) (i j) :
    (integerComplete R P x i j:ℝ)=complete (fun i => (R i:ℝ)) (fun j => (P j:ℝ))
      (fun i j => (x i j:ℝ)) i j := by
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [integerComplete,complete]

theorem integerComplete_nonneg (R : Fin (a+1) → ℕ) (P : Fin (c+1) → ℕ)
    (x : Fin a → Fin c → ℕ) :
    (∀ i j,0 ≤ integerComplete R P x i j) ↔
      ∀ i j,0 ≤ complete (fun i => (R i:ℝ)) (fun j => (P j:ℝ)) (fun i j => (x i j:ℝ)) i j := by
  simp only [← integerComplete_cast,Int.cast_nonneg_iff]

def tableOfFree (R : Fin (a+1) → ℕ) (P : Fin (c+1) → ℕ)
    (heq : (∑ i,R i)=∑ j,P j) (x : Fin a → Fin c → ℕ)
    (hx : ∀ i j,0 ≤ integerComplete R P x i j) : Tables R P := by
  refine ⟨fun i j => (integerComplete R P x i j).toNat,?_,?_⟩
  · intro i
    have hh := complete_row (fun i => (R i:ℝ)) (fun j => (P j:ℝ)) (fun i j => (x i j:ℝ)) i
    simp only [← integerComplete_cast] at hh
    have hc (j) : (((integerComplete R P x i j).toNat:ℕ):ℝ)=(integerComplete R P x i j:ℝ) := by
      rw [← Int.cast_natCast,Int.toNat_of_nonneg (hx i j)]
    exact_mod_cast (show (∑ j,((integerComplete R P x i j).toNat:ℝ))=(R i:ℝ) by simpa only [hc] using hh)
  · intro j
    have hreal : (∑ i,(R i:ℝ))=∑ j,(P j:ℝ) := by exact_mod_cast heq
    have hh := complete_col (fun i => (R i:ℝ)) (fun j => (P j:ℝ)) (fun i j => (x i j:ℝ)) hreal j
    simp only [← integerComplete_cast] at hh
    have hc (i) : (((integerComplete R P x i j).toNat:ℕ):ℝ)=(integerComplete R P x i j:ℝ) := by
      rw [← Int.cast_natCast,Int.toNat_of_nonneg (hx i j)]
    exact_mod_cast (show (∑ i,((integerComplete R P x i j).toNat:ℝ))=(P j:ℝ) by simpa only [hc] using hh)

@[simp] theorem tableOfFree_free (R : Fin (a+1) → ℕ) (P : Fin (c+1) → ℕ)
    (heq : (∑ i,R i)=∑ j,P j) (x : Fin a → Fin c → ℕ)
    (hx : ∀ i j,0 ≤ integerComplete R P x i j) (i j) :
    (tableOfFree R P heq x hx).val i.castSucc j.castSucc=x i j := by
  simp [tableOfFree,integerComplete]

theorem tables_free_injective (R : Fin (a+1) → ℕ) (P : Fin (c+1) → ℕ) :
    Function.Injective (fun X : Tables R P => fun i : Fin a => fun j : Fin c => X.val i.castSucc j.castSucc) := by
  intro X Y h
  have hx := complete_represents (fun i => (R i:ℝ)) (fun j => (P j:ℝ)) (fun i j => (X.val i j:ℝ))
    (fun i => by exact_mod_cast X.property.1 i) (fun j => by exact_mod_cast X.property.2 j)
  have hy := complete_represents (fun i => (R i:ℝ)) (fun j => (P j:ℝ)) (fun i j => (Y.val i j:ℝ))
    (fun i => by exact_mod_cast Y.property.1 i) (fun j => by exact_mod_cast Y.property.2 j)
  apply Subtype.ext
  funext i j
  have he : (fun i : Fin a => fun j : Fin c => (X.val i.castSucc j.castSucc:ℝ))=
      (fun i : Fin a => fun j : Fin c => (Y.val i.castSucc j.castSucc:ℝ)) := by
    funext i j; exact_mod_cast congrFun (congrFun h i) j
  rw [he,hy] at hx
  exact_mod_cast congrFun (congrFun hx i) j |>.symm

abbrev Offsets (w : Fin q → ℕ) := (i : Fin q) → Fin (w i)
abbrev Sample (w : Fin q → ℕ) := Vertex q K × Offsets w

def freeSample (e : Fin q ≃ Fin a×Fin c) (w : Fin q → ℕ) (s : Sample (K:=K) w) : Fin a → Fin c → ℕ :=
  fun i j => w (e.symm (i,j))*(s.1 (e.symm (i,j))).val+(s.2 (e.symm (i,j))).val

def samplePoint (w : Fin q → ℕ) (s : Sample (K:=K) w) : Fin q → ℝ :=
  fun i => (s.1 i:ℝ)+(s.2 i:ℝ)/w i

theorem samplePoint_mem (w : Fin q → ℕ) (hw : ∀ i,0<w i) (s : Sample (K:=K) w) :
    samplePoint w s∈closedBin s.1 := by
  intro i _
  have hi : (s.2 i:ℝ)<w i := by exact_mod_cast (s.2 i).isLt
  have hw' : (0:ℝ)<w i := by exact_mod_cast hw i
  change (s.1 i:ℝ) ≤ (s.1 i:ℝ)+(s.2 i:ℝ)/w i ∧ (s.1 i:ℝ)+(s.2 i:ℝ)/w i ≤ (s.1 i:ℝ)+1
  constructor
  · exact le_add_of_nonneg_right (by positivity)
  · linarith [((div_lt_one hw').mpr hi)]

theorem samplePoint_complete (e : Fin q ≃ Fin a×Fin c) (w : Fin q → ℕ) (hw : ∀ i,0<w i)
    (R : Fin (a+1) → ℕ) (P : Fin (c+1) → ℕ) (s : Sample (K:=K) w) :
    scaled (fun i => (R i:ℝ)) (fun j => (P j:ℝ)) (fun i j => (w (e.symm (i,j)):ℝ))
      (fun ij => samplePoint w s (e.symm ij))=
    complete (fun i => (R i:ℝ)) (fun j => (P j:ℝ)) (fun i j => (freeSample e w s i j:ℝ)) := by
  unfold scaled
  congr 1
  funext i j
  simp only [samplePoint,freeSample,Nat.cast_add,Nat.cast_mul,mul_add]
  rw [mul_div_cancel₀ _ (by exact_mod_cast (hw (e.symm (i,j))).ne')]

theorem freeSample_injective (e : Fin q ≃ Fin a×Fin c) (w : Fin q → ℕ) (hw : ∀ i,0<w i) :
    Function.Injective (freeSample (K:=K) e w) := by
  intro s t h
  have hh (i) : w i*(s.1 i).val+(s.2 i).val=w i*(t.1 i).val+(t.2 i).val := by
    have hi := congrFun (congrFun h (e i).1) (e i).2
    change w (e.symm (e i))*(s.1 (e.symm (e i))).val+(s.2 (e.symm (e i))).val =
      w (e.symm (e i))*(t.1 (e.symm (e i))).val+(t.2 (e.symm (e i))).val at hi
    rw [e.symm_apply_apply] at hi
    exact hi
  have hb (i) : (s.1 i).val=(t.1 i).val := by
    have hi := congrArg (fun z => z/w i) (hh i)
    simpa only [Nat.mul_add_div (hw i),Nat.div_eq_of_lt (s.2 i).isLt,Nat.div_eq_of_lt (t.2 i).isLt,Nat.add_zero] using hi
  apply Prod.ext
  · funext i; exact Fin.ext (hb i)
  · funext i; apply Fin.ext; have := hh i; rw [hb i] at this; omega

end
end Contingency.Dense

 

 

open scoped BigOperators
namespace Contingency.Dense
noncomputable section
open Contingency.Grid Contingency.Interpolation
variable {a c q K : ℕ}

theorem closedBin_corner_distance (v : Vertex q K) (x : Fin q → ℝ) (hx : x∈closedBin v) :
    ‖x-realCorner v‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
  intro i
  have hh := hx i (Set.mem_univ i)
  simp only [Set.mem_Icc] at hh
  simp only [Pi.sub_apply,realCorner,Real.norm_eq_abs,abs_le]
  constructor <;> linarith [hh.1,hh.2]

 
theorem feasible_bin_weight_one (e : Fin q ≃ Fin a×Fin c)
    (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ) (w : Fin a → Fin c → ℝ)
    (d : ℝ) (hd : 0<d) (he : (a*c:ℕ) ≤ d)
    (hR : ∀ i,0<R i) (hP : ∀ j,0<P j)
    (hRmax : ∀ i,R i ≤ R (Fin.last a)) (hPmax : ∀ j,P j ≤ P (Fin.last c))
    (hw0 : ∀ i j,0 ≤ w i j) (hw : ∀ i j,w i j ≤ scale R P i.castSucc j.castSucc/d^8)
    (v : Vertex q K) (x : Fin q → ℝ) (hx : x∈closedBin v)
    (hx0 : x∈region (constraints e R P w) 0) : binWeight e R P w d v=1 := by
  have hz : penalty R P w (d^8) d (fun s => realCorner v (e.symm s))=0 := by
    apply penalty_zero_of_slack
    intro i j
    have hh := constraints_lipschitz e R P w (d^8) d (by positivity) hd.le he hR hP hRmax hPmax hw0 hw
      x (realCorner v) (i,j)
    have hd' : 0 ≤ d/d^8 := by positivity
    have hdist := mul_le_mul_of_nonneg_left (closedBin_corner_distance v x hx) hd'
    have hf := hx0 (i,j)
    change 0 ≤ constraints e R P w (i,j) x at hf
    rw [neg_div]
    change -(d/d^8) ≤ constraints e R P w (i,j) (realCorner v)
    linarith only [(abs_le.mp hh).2,hdist,hf]
  simp [binWeight,exponentWeight,binExponent,hz]

def Accepted (e : Fin q ≃ Fin a×Fin c) (w : Fin q → ℕ)
    (R : Fin (a+1) → ℕ) (P : Fin (c+1) → ℕ) (s : Sample (K:=K) w) : Prop :=
  ∀ i j,0 ≤ integerComplete R P (freeSample e w s) i j

theorem accepted_iff_point (e : Fin q ≃ Fin a×Fin c) (w : Fin q → ℕ) (hw : ∀ i,0<w i)
    (R : Fin (a+1) → ℕ) (P : Fin (c+1) → ℕ) (hR : ∀ i,0<R i) (hP : ∀ j,0<P j)
    (s : Sample (K:=K) w) : Accepted e w R P s ↔
      samplePoint w s∈region (constraints e (fun i => (R i:ℝ)) (fun j => (P j:ℝ))
        (fun i j => (w (e.symm (i,j)):ℝ))) 0 := by
  rw [Accepted,integerComplete_nonneg]
  have hs (i j) : (0:ℝ)<scale (fun i => (R i:ℝ)) (fun j => (P j:ℝ)) i j :=
    lt_min (by dsimp; exact_mod_cast hR i) (by dsimp; exact_mod_cast hP j)
  constructor
  · intro h ij
    change 0 ≤ scaled _ _ _ _ ij.1 ij.2/scale _ _ _ _
    rw [samplePoint_complete e w hw R P s]
    exact div_nonneg (h _ _) (hs _ _).le
  · intro h i j
    have hi := h (i,j)
    change 0 ≤ scaled _ _ _ _ i j/scale _ _ _ _ at hi
    rw [samplePoint_complete e w hw R P s] at hi
    have hh := (le_div_iff₀ (hs i j)).mp hi
    simpa only [zero_mul] using hh

theorem safe_bin_accepted (e : Fin q ≃ Fin a×Fin c) (w : Fin q → ℕ) (hw : ∀ i,0<w i)
    (R : Fin (a+1) → ℕ) (P : Fin (c+1) → ℕ) (hR : ∀ i,0<R i) (hP : ∀ j,0<P j)
    (v : Vertex q K)
    (hv : v∈safeBins (constraints e (fun i => (R i:ℝ)) (fun j => (P j:ℝ))
      (fun i j => (w (e.symm (i,j)):ℝ)))) (β : Offsets w) : Accepted e w R P (v,β) := by
  apply (accepted_iff_point e w hw R P hR hP (v,β)).mpr
  exact (mem_safeBins _ v).mp hv (samplePoint_mem w hw (v,β))

 
theorem table_bin_bound (e : Fin q ≃ Fin a×Fin c) (w : Fin q → ℕ) (hw : ∀ i,0<w i)
    (R : Fin (a+1) → ℕ) (P : Fin (c+1) → ℕ) (B : ℝ) (hB : 0<B) (hK : 2*B<K)
    (hwidth : ∀ i,scale (fun i => (R i:ℝ)) (fun j => (P j:ℝ)) (e i).1.castSucc (e i).2.castSucc/(2*B) ≤ w i)
    (X : Tables R P) (i : Fin q) : X.val (e i).1.castSucc (e i).2.castSucc/w i<K := by
  have hh := entry_le_scale (fun i => (R i:ℝ)) (fun j => (P j:ℝ)) (fun i j => (X.val i j:ℝ))
    (fun i j => by positivity) (fun i => by exact_mod_cast X.property.1 i)
    (fun j => by exact_mod_cast X.property.2 j) (e i).1.castSucc (e i).2.castSucc
  have hw' : (0:ℝ)<w i := by exact_mod_cast hw i
  have hl := (div_le_iff₀ (by positivity : (0:ℝ)<2*B)).mp (hwidth i)
  have hu : (X.val (e i).1.castSucc (e i).2.castSucc:ℝ)<(w i:ℝ)*K := by nlinarith only [hh,hl,hK,hw']
  have hn : X.val (e i).1.castSucc (e i).2.castSucc<w i*K := by exact_mod_cast hu
  exact (Nat.div_lt_iff_lt_mul (hw i)).mpr (by simpa only [Nat.mul_comm] using hn)

def encodeSample (e : Fin q ≃ Fin a×Fin c) (w : Fin q → ℕ) (hw : ∀ i,0<w i)
    {R : Fin (a+1) → ℕ} {P : Fin (c+1) → ℕ}
    (bound : ∀ X : Tables R P,∀ i,X.val (e i).1.castSucc (e i).2.castSucc/w i<K)
    (X : Tables R P) : Sample (K:=K) w :=
  (fun i => ⟨X.val (e i).1.castSucc (e i).2.castSucc/w i,bound X i⟩,
   fun i => ⟨X.val (e i).1.castSucc (e i).2.castSucc%w i,Nat.mod_lt _ (hw i)⟩)

@[simp] theorem encodeSample_free (e : Fin q ≃ Fin a×Fin c) (w : Fin q → ℕ) (hw : ∀ i,0<w i)
    {R : Fin (a+1) → ℕ} {P : Fin (c+1) → ℕ}
    (bound : ∀ X : Tables R P,∀ i,X.val (e i).1.castSucc (e i).2.castSucc/w i<K)
    (X : Tables R P) : freeSample e w (encodeSample e w hw bound X)=
      fun i j => X.val i.castSucc j.castSucc := by
  funext i j
  simp only [freeSample,encodeSample,e.apply_symm_apply]
  exact Nat.div_add_mod _ _

theorem encodeSample_accepted (e : Fin q ≃ Fin a×Fin c) (w : Fin q → ℕ) (hw : ∀ i,0<w i)
    {R : Fin (a+1) → ℕ} {P : Fin (c+1) → ℕ}
    (bound : ∀ X : Tables R P,∀ i,X.val (e i).1.castSucc (e i).2.castSucc/w i<K)
    (X : Tables R P) : Accepted e w R P (encodeSample e w hw bound X) := by
  rw [Accepted,encodeSample_free,integerComplete_nonneg]
  have he := complete_represents (fun i => (R i:ℝ)) (fun j => (P j:ℝ)) (fun i j => (X.val i j:ℝ))
    (fun i => by exact_mod_cast X.property.1 i) (fun j => by exact_mod_cast X.property.2 j)
  rw [he]
  exact fun i j => Nat.cast_nonneg _

 
def acceptedEquiv (e : Fin q ≃ Fin a×Fin c) (w : Fin q → ℕ) (hw : ∀ i,0<w i)
    {R : Fin (a+1) → ℕ} {P : Fin (c+1) → ℕ} (heq : (∑ i,R i)=∑ j,P j)
    (bound : ∀ X : Tables R P,∀ i,X.val (e i).1.castSucc (e i).2.castSucc/w i<K) :
    {s : Sample (K:=K) w // Accepted e w R P s} ≃ Tables R P where
  toFun s := tableOfFree R P heq (freeSample e w s.val) s.property
  invFun X := ⟨encodeSample e w hw bound X,encodeSample_accepted e w hw bound X⟩
  left_inv s := by
    apply Subtype.ext
    apply freeSample_injective e w hw
    rw [encodeSample_free]
    funext i j
    exact tableOfFree_free R P heq _ s.property i j
  right_inv X := by
    apply tables_free_injective R P
    funext i j
    change (tableOfFree R P heq _ _).val i.castSucc j.castSucc = X.val i.castSucc j.castSucc
    exact (tableOfFree_free R P heq _ _ i j).trans
      (congrFun (congrFun (encodeSample_free e w hw bound X) i) j)

end
end Contingency.Dense

 

 

open scoped BigOperators
namespace Contingency.Dense
noncomputable section
open Contingency.Grid Contingency.Interpolation
variable {a c q K : ℕ}

 

structure BinProblem (a c q K : ℕ) where
  e : Fin q ≃ Fin a×Fin c
  R : Fin (a+1) → ℕ
  P : Fin (c+1) → ℕ
  w : Fin q → ℕ
  d : ℝ
  hd : 4 ≤ d
  hq : (q:ℝ) ≤ d
  ha : (a+1:ℕ) ≤ d
  hc : (c+1:ℕ) ≤ d
  hK : 2*d^8<K
  hR : ∀ i,0<R i
  hP : ∀ j,0<P j
  heq : (∑ i,R i)=∑ j,P j
  hRmax : ∀ i,R i ≤ R (Fin.last a)
  hPmax : ∀ j,P j ≤ P (Fin.last c)
  hw : ∀ i,0<w i
  hwlo : ∀ i,scale (fun i => (R i:ℝ)) (fun j => (P j:ℝ)) (e i).1.castSucc (e i).2.castSucc/(2*d^8) ≤ w i
  hwhi : ∀ i,(w i:ℝ) ≤ scale (fun i => (R i:ℝ)) (fun j => (P j:ℝ)) (e i).1.castSucc (e i).2.castSucc/d^8

namespace BinProblem
variable (D : BinProblem a c q K)

def widths (i : Fin a) (j : Fin c) : ℝ := D.w (D.e.symm (i,j))
def weight : Vertex q K → ℝ := binWeight D.e (fun i => (D.R i:ℝ)) (fun j => (D.P j:ℝ)) D.widths D.d
def Z : ℝ := ∑ v,D.weight v
def offsetCount : ℕ := Fintype.card (Offsets D.w)
def sampleMass (s : Sample (K:=K) D.w) : ℝ := D.weight s.1/(D.Z*D.offsetCount)
def good (s : Sample (K:=K) D.w) : Prop := Accepted D.e D.w D.R D.P s

def success : ℝ := by
  classical
  exact ∑ s : Sample (K:=K) D.w,if D.good s then D.sampleMass s else 0

theorem offsetCount_pos : 0<D.offsetCount := by
  let : Nonempty (Offsets D.w) := ⟨fun i => ⟨0,D.hw i⟩⟩
  exact Fintype.card_pos

include D in
theorem Kpos : 0<K := by
  have hd : 0<D.d := by linarith [D.hd]
  have hk : (0:ℝ)<K := (by positivity : (0:ℝ)<2*D.d^8).trans D.hK
  exact_mod_cast hk

theorem weight_pos (v : Vertex q K) : 0<D.weight v := exponentWeight_pos _ _

theorem Zpos : 0<D.Z := by
  let : Nonempty (Vertex q K) := ⟨fun _ => ⟨0,D.Kpos⟩⟩
  exact Finset.sum_pos (fun v _ => D.weight_pos v) Finset.univ_nonempty

theorem sampleMass_nonneg (s : Sample (K:=K) D.w) : 0 ≤ D.sampleMass s := by
  apply div_nonneg (D.weight_pos s.1).le
  exact mul_nonneg D.Zpos.le (Nat.cast_nonneg _)

theorem sampleMass_total : (∑ s : Sample (K:=K) D.w,D.sampleMass s)=1 := by
  simp only [sampleMass,Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    ← Finset.sum_div,← Finset.mul_sum]
  change (D.offsetCount:ℝ)*D.Z/(D.Z*D.offsetCount)=1
  field_simp [D.Zpos.ne',Nat.cast_ne_zero.mpr D.offsetCount_pos.ne']

theorem widthlo (i j) : scale (fun i => (D.R i:ℝ)) (fun j => (D.P j:ℝ))
    i.castSucc j.castSucc/(2*D.d^8) ≤ D.widths i j := by
  simpa only [widths,D.e.apply_symm_apply] using D.hwlo (D.e.symm (i,j))

theorem widthhi (i j) : D.widths i j ≤ scale (fun i => (D.R i:ℝ)) (fun j => (D.P j:ℝ))
    i.castSucc j.castSucc/D.d^8 := by
  simpa only [widths,D.e.apply_symm_apply] using D.hwhi (D.e.symm (i,j))

theorem dim : (a*c:ℕ) ≤ D.d := by
  have he : q=a*c := by simpa using Fintype.card_congr D.e
  simpa only [he] using D.hq

theorem accepted_weight (s : Sample (K:=K) D.w) (hs : D.good s) : D.weight s.1=1 := by
  apply feasible_bin_weight_one D.e _ _ _ D.d (by linarith [D.hd]) D.dim
    (fun i => by exact_mod_cast D.hR i) (fun j => by exact_mod_cast D.hP j)
    (fun i => by exact_mod_cast D.hRmax i) (fun j => by exact_mod_cast D.hPmax j)
    (fun i j => by exact Nat.cast_nonneg _) D.widthhi s.1 (samplePoint D.w s)
    (samplePoint_mem D.w D.hw s)
  exact (accepted_iff_point D.e D.w D.hw D.R D.P D.hR D.hP s).mp hs

def safe : Finset (Vertex q K) := safeBins (constraints D.e (fun i => (D.R i:ℝ)) (fun j => (D.P j:ℝ)) D.widths)

theorem safe_count : D.Z/32 ≤ (D.safe.card:ℝ) := by
  exact dense_safe_bin_bound D.e _ _ D.widths D.d D.hd D.hq D.ha D.hc D.hK
    (fun i => by exact_mod_cast D.hR i) (fun j => by exact_mod_cast D.hP j)
    (by exact_mod_cast D.heq)
    (fun i => by exact_mod_cast D.hRmax i) (fun j => by exact_mod_cast D.hPmax j)
    D.widthlo D.widthhi

theorem safe_success (v : Vertex q K) (hv : v∈D.safe) (β : Offsets D.w) : D.good (v,β) :=
  safe_bin_accepted D.e D.w D.hw D.R D.P D.hR D.hP v hv β

 
theorem success_lower : 1/32 ≤ D.success := by
  classical
  have hl : (D.safe.card:ℝ)/D.Z ≤ D.success := by
    calc
      _ = ∑ v∈D.safe,∑ β : Offsets D.w,D.sampleMass (v,β) := by
        have hw (v) (hv : v∈D.safe) : D.weight v=1 :=
          D.accepted_weight (v,fun i => ⟨0,D.hw i⟩) (D.safe_success v hv _)
        simp only [sampleMass]
        rw [Finset.sum_congr rfl (fun v hv => by rw [hw v hv])]
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        change (D.safe.card:ℝ)/D.Z=(D.safe.card:ℝ)*((D.offsetCount:ℝ)*(1/(D.Z*D.offsetCount)))
        field_simp [D.Zpos.ne',Nat.cast_ne_zero.mpr D.offsetCount_pos.ne']
      _ = ∑ v∈D.safe,∑ β : Offsets D.w,if D.good (v,β) then D.sampleMass (v,β) else 0 := by
        apply Finset.sum_congr rfl; intro v hv
        apply Finset.sum_congr rfl; intro β _
        rw [ite_eq_left (D.safe_success v hv β)]
      _ ≤ ∑ v,∑ β : Offsets D.w,if D.good (v,β) then D.sampleMass (v,β) else 0 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro v _ _
        exact Finset.sum_nonneg (fun β _ => by split_ifs; exact D.sampleMass_nonneg _; rfl)
      _ = D.success := by simp only [success,Fintype.sum_prod_type]
  apply le_trans _ hl
  apply (le_div_iff₀ D.Zpos).mpr
  linarith [D.safe_count]

theorem success_upper : D.success ≤ 1 := by
  rw [← D.sampleMass_total]
  apply Finset.sum_le_sum
  intro s _
  split_ifs
  · rfl
  · exact D.sampleMass_nonneg s

theorem bound (X : Tables D.R D.P) (i : Fin q) : X.val (D.e i).1.castSucc (D.e i).2.castSucc/D.w i<K :=
  table_bin_bound D.e D.w D.hw D.R D.P (D.d^8) (by have := D.hd; positivity) D.hK D.hwlo X i

def tableSample (X : Tables D.R D.P) : Sample (K:=K) D.w := encodeSample D.e D.w D.hw D.bound X

 
theorem table_mass (X : Tables D.R D.P) : D.sampleMass (D.tableSample X)=1/(D.Z*D.offsetCount) := by
  unfold sampleMass tableSample
  rw [D.accepted_weight _ (encodeSample_accepted D.e D.w D.hw D.bound X)]

 
theorem success_eq_card : D.success=Nat.card (Tables D.R D.P)/(D.Z*D.offsetCount) := by
  classical
  rw [success,← Finset.sum_filter]
  rw [Finset.sum_subtype (p:=D.good) _ (by intro s; simp) D.sampleMass]
  have hm (s : {s : Sample (K:=K) D.w // D.good s}) : D.sampleMass s.val=1/(D.Z*D.offsetCount) := by
    unfold sampleMass
    rw [D.accepted_weight s.val s.property]
  simp only [hm,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hcard : Fintype.card {s : Sample (K:=K) D.w // D.good s}=Nat.card (Tables D.R D.P) := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (acceptedEquiv D.e D.w D.hw D.heq D.bound)
  rw [hcard]
  ring

 
theorem conditional_uniform (X : Tables D.R D.P) :
    D.sampleMass (D.tableSample X)/D.success=1/Nat.card (Tables D.R D.P) := by
  have hs : 0<D.success := lt_of_lt_of_le (by norm_num) D.success_lower
  have hn : 0<(Nat.card (Tables D.R D.P):ℝ) := by
    rw [D.success_eq_card] at hs
    have hd : 0<D.Z*(D.offsetCount:ℝ) := mul_pos D.Zpos (by exact_mod_cast D.offsetCount_pos)
    simpa only [zero_mul] using (lt_div_iff₀ hd).mp hs
  rw [D.table_mass,D.success_eq_card]
  field_simp [D.Zpos.ne',Nat.cast_ne_zero.mpr D.offsetCount_pos.ne',hn.ne']

end BinProblem
end
end Contingency.Dense

end

end OAI
