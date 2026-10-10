import OAI.MathematicalPhysics.Heisenberg.CyclicEnergy

namespace OAI

noncomputable section

open Filter Topology
open scoped RealInnerProductSpace Classical
open scoped Classical
open Filter

open scoped BigOperators Classical

namespace Heisenberg.Exposure
variable {I J B : Type*} [Fintype I] [Fintype J] [Fintype B]

theorem product_marginal (w : I → B → ℝ) (hw : ∀ i,∑ b,w i b=1)
    (r : J → I) (hr : Function.Injective r) (F : (J → B) → ℝ) :
    (∑ c : I → B,productWeight w c*F (c ∘ r)) =
      ∑ c : J → B,productWeight (fun j => w (r j)) c * F c := by
  let M : I → Prop := fun i => i∈Set.range r
  let e : J ≃ {i // M i} := Equiv.ofInjective r hr
  let q := Equiv.piEquivPiSubtypeProd M (fun _ => B)
  rw [←q.symm.sum_comp,Fintype.sum_prod_type]
  have he (a : {i // M i} → B) (b : {i // ¬M i} → B) :
      q.symm (a,b) ∘ r = a ∘ e := by
    funext j
    exact merge_left M a b (e j)
  simp only [he]
  change (∑ a,∑ b,productWeight w (merge M a b)*F (a ∘ e))=_
  simp_rw [productWeight_merge,mul_right_comm _ _ (F _),←Finset.mul_sum]
  have hs : (∑ b : {i // ¬M i} → B,
      productWeight (fun i : {i // ¬M i} => w i) b)=1 :=
    by simp only [productWeight, ←Fintype.prod_sum, hw, Finset.prod_const_one]
  simp only [hs,mul_one]
  let e' : ({i // M i} → B) ≃ (J → B) := Equiv.piCongrLeft (fun _ => B) e.symm
  rw [←e'.sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  have hf : e' a=a ∘ e := by
    funext j
    simp [e', Equiv.piCongrLeft_apply]
  rw [hf]
  congr 1
  unfold productWeight
  convert (e.prod_comp (fun i => w i (a i))).symm using 1
  · congr 1
    ext j
    simp
  · apply Finset.prod_congr rfl
    intro j _
    rfl

end Heisenberg.Exposure

namespace Heisenberg.Serial

section
open Heisenberg.Exposure Heisenberg.MeshPair
variable {V B I : Type*} [Fintype V] [DecidableEq V] [Fintype B] [Fintype I]

theorem mean_walkKernel (n : ℕ) (w : Fin n → B → ℝ)
    (D : Fin (n+1) → Set V) (σ : Fin n → B → Equiv.Perm V) :
    (∑ c : Fin n → B,(productWeight w c) • walkKernel n D (fun i => σ i (c i))) =
      product n (fun i => ∑ b,w i b • killedBetween (D i.castSucc) (D i.succ) (σ i b)) *
        projection (D 0) := by
  simp only [walkKernel, ←Matrix.smul_mul, ←Finset.sum_mul]
  congr 1
  exact mean_product n w (fun i b => killedBetween (D i.castSucc) (D i.succ) (σ i b))

theorem prefix_mean (n : ℕ) (w : I → B → ℝ) (hw : ∀ i,∑ b,w i b=1)
    (r : Fin n → I) (hr : Function.Injective r) (D : Fin (n+1) → Set V)
    (σ : Fin n → B → Equiv.Perm V) (x y : V) :
    (∑ c : I → B,productWeight w c * walkKernel n D (fun i => σ i (c (r i))) x y) =
      (product n (fun i => ∑ b,w (r i) b • killedBetween (D i.castSucc) (D i.succ) (σ i b)) *
        projection (D 0)) x y := by
  have h := product_marginal w hw r hr
    (fun c => walkKernel n D (fun i => σ i (c i)) x y)
  change (∑ c,productWeight w c * (fun c => walkKernel n D (fun i => σ i (c i)) x y) (c ∘ r)) = _
  rw [h]
  have he := congrArg (fun A : Matrix V V ℝ => A x y)
    (mean_walkKernel n (fun i => w (r i)) D σ)
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul] at he
  convert he using 1
  congr 1
  ext c
  simp

theorem prefix_endpoint_bound (n : ℕ) (w : I → B → ℝ)
    (hw : ∀ i,∑ b,w i b=1) (hw0 : ∀ i b,0≤w i b)
    (r : Fin n → I) (hr : Function.Injective r) (D : Fin (n+1) → Set V)
    (σ : Fin n → B → Equiv.Perm V) (j : V) (A : Set V) :
    (∑ i,if i∈A then
      (product n (fun k => ∑ b,w (r k) b • killedBetween (D k.castSucc) (D k.succ) (σ k b)) *
        projection (D 0)) i j else 0) ≤
      ∑ c : I → B,if follow n (fun k => σ k (c (r k))) j∈A then productWeight w c else 0 := by
  simp_rw [←prefix_mean n w hw r hr D σ]
  have hf (i : V) : (if i∈A then ∑ c,productWeight w c * walkKernel n D (fun k => σ k (c (r k))) i j else 0) =
      ∑ c,productWeight w c * (if i∈A then walkKernel n D (fun k => σ k (c (r k))) i j else 0) := by
    by_cases hi : i∈A <;> simp [hi]
  simp only [hf]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro c _
  rw [←Finset.mul_sum]
  have hn := productWeight_nonneg w hw0 c
  simp only [walkKernel_apply]
  by_cases hs : survives n D (fun k => σ k (c (r k))) j
  · simp only [hs,ite_true]
    rw [Finset.sum_eq_single (follow n (fun k => σ k (c (r k))) j)]
    · by_cases ha : follow n (fun k => σ k (c (r k))) j∈A <;> simp [ha]
    · intro i _ hi
      simp [hi]
    · simp
  · simp only [hs,ite_false,ite_self,Finset.sum_const_zero,mul_zero]
    split_ifs <;> positivity

end

open Heisenberg.Exposure
variable {V : Type*}

lemma follow_snoc (n : ℕ) (σ : Fin (n+1) → Equiv.Perm V) (v : V) :
    follow (n+1) σ v=σ (Fin.last n) (follow n (fun i=>σ i.castSucc) v) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [follow,ih]
    rfl

lemma follow_trajectory (τ : ℕ → Equiv.Perm V) (c : ℕ → Bool) (n : ℕ) (v : V) :
    follow n (fun i => if c i then τ i else 1) v=trajectory τ c n v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [follow_snoc]
    change (if c n then τ n else 1) (follow n (fun i => if c i then τ i else 1) v) = _
    rw [ih,trajectory_succ]
    split_ifs <;> rfl

end Heisenberg.Serial

open scoped BigOperators Classical

open scoped BigOperators Classical
namespace Heisenberg.Clocks

def WeakTimes (n r : ℕ) := {f : Fin r → Fin n // Monotone f}
instance (n r : ℕ) : Fintype (WeakTimes n r) := inferInstanceAs (Fintype {f : Fin r → Fin n // Monotone f})

def shifted {n r : ℕ} (f : WeakTimes n r) (i : Fin r) : Fin (n+r) :=
  ⟨(f.val i).val+i.val, by have h := (f.val i).isLt; have hi := i.isLt; omega⟩

lemma shifted_strictMono {n r : ℕ} (f : WeakTimes n r) : StrictMono (shifted f) := by
  intro i j hij
  have h := f.property hij.le
  have h' : (f.val i).val ≤ (f.val j).val := h
  change (f.val i).val+i.val < (f.val j).val+j.val
  have hij' : i.val < j.val := hij
  omega

def timeSet {n r : ℕ} (f : WeakTimes n r) : Finset (Fin (n+r)) :=
  Finset.univ.image (shifted f)

lemma timeSet_card {n r : ℕ} (f : WeakTimes n r) : (timeSet f).card = r := by
  rw [timeSet,Finset.card_image_of_injective _ (shifted_strictMono f).injective]
  simp

lemma timeSet_injective {n r : ℕ} : Function.Injective (timeSet (n:=n) (r:=r)) := by
  intro f g he
  have hr : Set.range (shifted f) = Set.range (shifted g) := by
    have hh := congrArg (fun s : Finset (Fin (n+r)) => (s : Set (Fin (n+r)))) he
    simpa only [timeSet,Finset.coe_image,Finset.coe_univ,Set.image_univ] using hh
  have hf := ((shifted_strictMono f).range_inj_of_wellFoundedLT (shifted_strictMono g)).mp hr
  apply Subtype.ext
  funext i
  have hh := congrArg (fun f : Fin r → Fin (n+r) => (f i).val) hf
  apply Fin.ext
  change (f.val i).val+i.val = (g.val i).val+i.val at hh
  omega

theorem card_weakTimes_le (n r : ℕ) : Fintype.card (WeakTimes n r) ≤ (n+r).choose r := by
  let e : WeakTimes n r → {s : Finset (Fin (n+r)) // s ∈ Finset.univ.powersetCard r} :=
    fun f => ⟨timeSet f,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,timeSet_card f⟩⟩
  have he : Function.Injective e := fun f g h => timeSet_injective (congrArg Subtype.val h)
  have hc := Fintype.card_le_of_injective e he
  simpa only [Fintype.card_coe,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin] using hc

lemma weakTimes_weight_bound (n r : ℕ) {δ K : ℝ} (hδ : 0 ≤ δ) (hK : 0 ≤ K) :
    (Fintype.card (WeakTimes n r) : ℝ)*(K*δ)^r ≤ (K*((n:ℝ)+r)*δ)^r/(r.factorial:ℝ) := by
  have hc : (Fintype.card (WeakTimes n r) : ℝ) ≤ ((n+r).choose r : ℝ) := by
    exact_mod_cast card_weakTimes_le n r
  have hh := hc.trans (Nat.choose_le_pow_div (α:=ℝ) r (n+r))
  have hm := mul_le_mul_of_nonneg_right hh (pow_nonneg (mul_nonneg hK hδ) r)
  calc
    _ ≤ ((n+r:ℕ):ℝ)^r/(r.factorial:ℝ)*(K*δ)^r := hm
    _ = _ := by push_cast; rw [div_mul_eq_mul_div,← mul_pow]; congr 2; ring

theorem chronological_bound_limit (r : ℕ) (t K : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => (K*((n:ℝ)+r)*(t/(n:ℝ)))^r/(r.factorial:ℝ))
      Filter.atTop (nhds ((K*t)^r/(r.factorial:ℝ))) := by
  have hi : Filter.Tendsto (fun n : ℕ => (n:ℝ)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have he : ∀ᶠ n : ℕ in Filter.atTop,
      K*((n:ℝ)+r)*(t/(n:ℝ)) = K*t*(1+(r:ℝ)*(n:ℝ)⁻¹) := by
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    field_simp
  apply Filter.Tendsto.congr' (he.mono (fun n h => by rw [h]))
  convert ((tendsto_const_nhds.mul (tendsto_const_nhds.add (tendsto_const_nhds.mul hi))).pow r).div_const (r.factorial:ℝ) using 1; simp

variable {X E : Type*}

def edgeWords (choices : X → Finset E) (next : X → E → X) : ℕ → X → Finset (List E)
  | 0,_ => {[]}
  | r+1,x => (choices x).biUnion (fun e => (edgeWords choices next r (next x e)).image (List.cons e))

lemma mem_edgeWords_zero (choices : X → Finset E) (next : X → E → X) (x : X) (l : List E) :
    l ∈ edgeWords choices next 0 x ↔ l=[] := by simp [edgeWords]

lemma mem_edgeWords_cons (choices : X → Finset E) (next : X → E → X) (r : ℕ)
    (x : X) (e : E) (l : List E) :
    e::l ∈ edgeWords choices next (r+1) x ↔
      e ∈ choices x ∧ l ∈ edgeWords choices next r (next x e) := by
  simp [edgeWords]

lemma edgeWords_length (choices : X → Finset E) (next : X → E → X) (r : ℕ)
    (x : X) {l : List E} (hl : l ∈ edgeWords choices next r x) : l.length=r := by
  induction r generalizing x l with
  | zero => simpa only [(mem_edgeWords_zero choices next x l).mp hl] using List.length_nil
  | succ r ih =>
    obtain ⟨e,_he,himage⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨l',hl',heq⟩ := Finset.mem_image.mp himage
    rw [←heq]
    simpa using congrArg Nat.succ (ih (next x e) hl')

lemma card_edgeWords (choices : X → Finset E) (next : X → E → X) (B : ℕ)
    (hB : ∀ x,(choices x).card ≤ B) (r : ℕ) (x : X) :
    (edgeWords choices next r x).card ≤ B^r := by
  induction r generalizing x with
  | zero => simp [edgeWords]
  | succ r ih =>
    calc
      _ ≤ ∑ e ∈ choices x, ((edgeWords choices next r (next x e)).image (List.cons e)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _e ∈ choices x,B^r := Finset.sum_le_sum (fun e _ => (Finset.card_image_le).trans (ih _))
      _ = (choices x).card*B^r := by simp
      _ ≤ B*B^r := Nat.mul_le_mul_right _ (hB x)
      _ = _ := (pow_succ' _ _).symm

def Follows (choices : X → Finset E) (next : X → E → X) : X → List E → Prop
  | _,[] => True
  | x,e::l => e ∈ choices x ∧ Follows choices next (next x e) l

lemma follows_mem (choices : X → Finset E) (next : X → E → X) (x : X) (l : List E)
    (hl : Follows choices next x l) : l ∈ edgeWords choices next l.length x := by
  induction l generalizing x with
  | nil => simp [edgeWords]
  | cons e l ih => exact (mem_edgeWords_cons choices next l.length x e l).mpr ⟨hl.1,ih _ hl.2⟩

end Heisenberg.Clocks

end

end OAI
