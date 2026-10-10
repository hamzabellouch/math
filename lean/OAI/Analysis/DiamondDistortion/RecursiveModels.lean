import OAI.Analysis.DiamondDistortion.CoordinateSpace

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace RecursiveModel

section
open scoped ENNReal

/-- Coordinates on the root-including, countably branching height-h tree. -/
abbrev Coord : ℕ → Type
  | 0 => Unit
  | h+1 => Unit ⊕ (ℕ × Coord h)
abbrev Vec (h : ℕ) := Coord h →₀ ℝ

def rootChildren (h : ℕ) : Vec (h+1) ≃ₗ[ℝ] ℝ × (ℕ →₀ Vec h) :=
  (Finsupp.sumFinsuppLEquivProdFinsupp ℝ).trans
    ((Finsupp.uniqueLinearEquiv ℝ ℝ ()).prodCongr (Finsupp.curryLinearEquiv ℝ))

def finiteLp {ι : Type*} (p : ℝ≥0∞) (f : ι →₀ ℝ) : lp (fun _ : ι => ℝ) p :=
  ⟨(fun i => f i),(memℓp_zero f.hasFiniteSupport).of_exponent_ge bot_le⟩
@[simp] lemma finiteLp_apply {ι : Type*} (p : ℝ≥0∞) (f : ι →₀ ℝ) (i : ι) : finiteLp p f i=f i := rfl
@[simp] lemma finiteLp_zero {ι : Type*} (p : ℝ≥0∞) : finiteLp p (0 : ι →₀ ℝ)=0 := by ext i; rfl
@[simp] lemma finiteLp_add {ι : Type*} (p : ℝ≥0∞) (f g : ι →₀ ℝ) :
    finiteLp p (f+g)=finiteLp p f+finiteLp p g := by ext i; rfl
@[simp] lemma finiteLp_smul {ι : Type*} (p : ℝ≥0∞) (c : ℝ) (f : ι →₀ ℝ) :
    finiteLp p (c • f)=c • finiteLp p f := by ext i; rfl

def aggregate {ι : Type*} (p : ℝ≥0∞) (f : ι →₀ ℝ) : ℝ := ‖finiteLp p f‖
@[simp] lemma aggregate_zero {ι : Type*} (p : ℝ≥0∞) : aggregate p (0 : ι →₀ ℝ)=0 := by simp [aggregate]
lemma aggregate_nonneg {ι : Type*} (p : ℝ≥0∞) (f : ι →₀ ℝ) : 0 ≤ aggregate p f := lp.norm_nonneg' _
lemma aggregate_add {ι : Type*} (p : ℝ≥0∞) [Fact (1 ≤ p)] (f g : ι →₀ ℝ) :
    aggregate p (f+g) ≤ aggregate p f+aggregate p g := by simpa [aggregate] using norm_add_le (finiteLp p f) (finiteLp p g)
lemma aggregate_smul {ι : Type*} (p : ℝ≥0∞) [Fact (1 ≤ p)] (c : ℝ) (f : ι →₀ ℝ) :
    aggregate p (c • f)=|c| * aggregate p f := by simp [aggregate,norm_smul,Real.norm_eq_abs]
lemma aggregate_mono {ι : Type*} (p : ℝ≥0∞) [Fact (1 ≤ p)] (f g : ι →₀ ℝ)
    (hf : ∀ i,0 ≤ f i) (hfg : ∀ i,f i ≤ g i) : aggregate p f ≤ aggregate p g := by
  apply lp.norm_mono (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out))
  intro i
  simpa only [finiteLp_apply,Real.norm_eq_abs,abs_of_nonneg (hf i),abs_of_nonneg ((hf i).trans (hfg i))] using hfg i
lemma coordinate_le_aggregate {ι : Type*} (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : ι →₀ ℝ) (i : ι) :
    |f i| ≤ aggregate p f := by
  simpa only [finiteLp_apply,Real.norm_eq_abs,aggregate] using lp.norm_apply_le_norm (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) (finiteLp p f) i

/-- Least nonnegative upper arrays evaluated at the root. P and Q are kept
    separately; changing their root combination changes the norm. -/
def upper (p : ℝ≥0∞) : (h : ℕ) → ZeroHom (Vec h) (ℝ × ℝ)
  | 0 => ⟨fun v => (max (v ()) 0,max (-v ()) 0),by simp only [Finsupp.zero_apply,neg_zero,max_self]; rfl⟩
  | h+1 =>
      let U := upper p h
      let P (v : ℕ →₀ Vec h) := v.mapRange (fun z => (U z).1) (by simp)
      let Q (v : ℕ →₀ Vec h) := v.mapRange (fun z => (U z).2) (by simp)
      ⟨fun w => let v := rootChildren h w;
        (max (aggregate p (P v.2)) (v.1+aggregate p (Q v.2)),
        max (aggregate p (P v.2)-v.1) (aggregate p (Q v.2))),by
          simp only [map_zero,Prod.fst_zero,Prod.snd_zero,P,Q,Finsupp.mapRange_zero,aggregate_zero,add_zero,sub_zero,max_self]
          rfl⟩

@[simp] lemma upper_zero (p : ℝ≥0∞) (h : ℕ) : upper p h 0=0 := map_zero _
lemma upper_nonneg (p : ℝ≥0∞) (h : ℕ) (v : Vec h) :
    0 ≤ (upper p h v).1 ∧ 0 ≤ (upper p h v).2 := by
  cases h with
  | zero => exact ⟨le_max_right _ _,le_max_right _ _⟩
  | succ h => exact ⟨(aggregate_nonneg _ _).trans (le_max_left _ _),(aggregate_nonneg _ _).trans (le_max_right _ _)⟩

lemma upper_neg (p : ℝ≥0∞) (h : ℕ) (v : Vec h) :
    upper p h (-v)=((upper p h v).2,(upper p h v).1) := by
  induction h with
  | zero => simp only [upper,ZeroHom.coe_mk,Finsupp.neg_apply,neg_neg]
  | succ h ih =>
    let w := rootChildren h v
    let U := upper p h
    have hP : ((-w).2.mapRange (fun z => (U z).1) (by simp))=
        w.2.mapRange (fun z => (U z).2) (by simp) := by
      ext i
      change (upper p h (-w.2 i)).1=(upper p h (w.2 i)).2
      rw [ih]
    have hQ : ((-w).2.mapRange (fun z => (U z).2) (by simp))=
        w.2.mapRange (fun z => (U z).1) (by simp) := by
      ext i
      change (upper p h (-w.2 i)).2=(upper p h (w.2 i)).1
      rw [ih]
    dsimp only [upper,ZeroHom.coe_mk]
    rw [map_neg]
    change (max (aggregate p _) ((-w).1+aggregate p _),max (aggregate p _-(-w).1) (aggregate p _))=_
    rw [hP,hQ]
    dsimp only [Prod.fst_neg]
    ext <;> dsimp only [Prod.fst,Prod.snd]
    · rw [max_comm]; congr 1; ring
    · rw [max_comm]; congr 1; ring

/-- A node's two least upper values once its child arrays have norms a,b. -/
def join (r a b : ℝ) : ℝ × ℝ := (max a (r+b),max (a-r) b)
lemma join_mono {r a b A B : ℝ} (ha : a ≤ A) (hb : b ≤ B) :
    (join r a b).1 ≤ (join r A B).1 ∧ (join r a b).2 ≤ (join r A B).2 := by
  exact ⟨max_le_max ha (add_le_add_right hb _),max_le_max (sub_le_sub_right ha _) hb⟩
lemma join_add (r s a b c d : ℝ) :
    (join (r+s) (a+c) (b+d)).1 ≤ (join r a b).1+(join s c d).1 ∧
    (join (r+s) (a+c) (b+d)).2 ≤ (join r a b).2+(join s c d).2 := by
  dsimp [join]
  constructor
  · apply max_le
    · exact add_le_add (le_max_left _ _) (le_max_left _ _)
    · linarith [le_max_right a (r+b),le_max_right c (s+d)]
  · apply max_le
    · linarith [le_max_left (a-r) b,le_max_left (c-s) d]
    · exact add_le_add (le_max_right _ _) (le_max_right _ _)
lemma join_smul (t r a b : ℝ) (ht : 0 ≤ t) :
    join (t*r) (t*a) (t*b)=t • join r a b := by
  ext <;> simp only [join,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  · rw [← mul_add,← mul_max_of_nonneg _ _ ht]
  · rw [← mul_sub,← mul_max_of_nonneg _ _ ht]
lemma join_root_bound (r a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |r| ≤ (join r a b).1+(join r a b).2 := by
  dsimp [join]
  rw [abs_le]
  constructor <;> linarith [le_max_left a (r+b),le_max_right a (r+b),le_max_left (a-r) b,le_max_right (a-r) b]

lemma upper_add (p : ℝ≥0∞) [Fact (1 ≤ p)] (h : ℕ) (v w : Vec h) :
    (upper p h (v+w)).1 ≤ (upper p h v).1+(upper p h w).1 ∧
    (upper p h (v+w)).2 ≤ (upper p h v).2+(upper p h w).2 := by
  induction h with
  | zero =>
    change max (v ()+w ()) 0 ≤ max (v ()) 0+max (w ()) 0 ∧
      max (-(v ()+w ())) 0 ≤ max (-v ()) 0+max (-w ()) 0
    constructor <;> apply max_le
    · exact add_le_add (le_max_left _ _) (le_max_left _ _)
    · exact add_nonneg (le_max_right _ _) (le_max_right _ _)
    · linarith [le_max_left (-v ()) 0,le_max_left (-w ()) 0]
    · exact add_nonneg (le_max_right _ _) (le_max_right _ _)
  | succ h ih =>
    let V := rootChildren h v
    let W := rootChildren h w
    let P (v : ℕ →₀ Vec h) := v.mapRange (fun z => (upper p h z).1) (by simp)
    let Q (v : ℕ →₀ Vec h) := v.mapRange (fun z => (upper p h z).2) (by simp)
    have hp : aggregate p (P (V.2+W.2)) ≤ aggregate p (P V.2)+aggregate p (P W.2) := by
      refine (aggregate_mono p _ _ ?_ ?_).trans (aggregate_add p _ _)
      · intro i; exact (upper_nonneg p h _).1
      · intro i; exact (ih _ _).1
    have hq : aggregate p (Q (V.2+W.2)) ≤ aggregate p (Q V.2)+aggregate p (Q W.2) := by
      refine (aggregate_mono p _ _ ?_ ?_).trans (aggregate_add p _ _)
      · intro i; exact (upper_nonneg p h _).2
      · intro i; exact (ih _ _).2
    have hm := join_mono (r := V.1+W.1) hp hq
    have ha := join_add V.1 W.1 (aggregate p (P V.2)) (aggregate p (Q V.2))
      (aggregate p (P W.2)) (aggregate p (Q W.2))
    dsimp only [upper,ZeroHom.coe_mk]
    rw [map_add]
    exact ⟨hm.1.trans ha.1,hm.2.trans ha.2⟩

lemma upper_smul_nonneg (p : ℝ≥0∞) [Fact (1 ≤ p)] (h : ℕ) (v : Vec h) (t : ℝ) (ht : 0 ≤ t) :
    upper p h (t • v)=t • upper p h v := by
  induction h with
  | zero =>
    dsimp only [upper,ZeroHom.coe_mk]
    change (max (t*v ()) 0,max (-(t*v ())) 0)=(t*max (v ()) 0,t*max (-v ()) 0)
    rw [mul_max_of_nonneg _ _ ht,mul_max_of_nonneg _ _ ht,mul_zero,mul_neg]
  | succ h ih =>
    let V := rootChildren h v
    let P (v : ℕ →₀ Vec h) := v.mapRange (fun z => (upper p h z).1) (by simp)
    let Q (v : ℕ →₀ Vec h) := v.mapRange (fun z => (upper p h z).2) (by simp)
    have hp : P (t • V.2)=t • P V.2 := by
      ext i
      change (upper p h (t • V.2 i)).1=t*(upper p h (V.2 i)).1
      rw [ih]; rfl
    have hq : Q (t • V.2)=t • Q V.2 := by
      ext i
      change (upper p h (t • V.2 i)).2=t*(upper p h (V.2 i)).2
      rw [ih]; rfl
    dsimp only [upper,ZeroHom.coe_mk]
    rw [map_smul]
    change join (t*V.1) (aggregate p (P (t • V.2))) (aggregate p (Q (t • V.2)))=t • join V.1 (aggregate p (P V.2)) (aggregate p (Q V.2))
    rw [hp,hq,aggregate_smul,aggregate_smul,abs_of_nonneg ht]
    exact join_smul _ _ _ _ ht

lemma upper_child_bound (p : ℝ≥0∞) [Fact (1 ≤ p)] (h : ℕ) (v : Vec (h+1)) (i : ℕ) :
    (upper p h ((rootChildren h v).2 i)).1 ≤ (upper p (h+1) v).1 ∧
    (upper p h ((rootChildren h v).2 i)).2 ≤ (upper p (h+1) v).2 := by
  let P := (rootChildren h v).2.mapRange (fun z => (upper p h z).1) (by simp)
  let Q := (rootChildren h v).2.mapRange (fun z => (upper p h z).2) (by simp)
  have hp := coordinate_le_aggregate p P i
  have hq := coordinate_le_aggregate p Q i
  constructor
  · exact (le_abs_self _).trans (hp.trans (le_max_left _ _))
  · exact (le_abs_self _).trans (hq.trans (le_max_right _ _))

lemma upper_coordinate_bound (p : ℝ≥0∞) [Fact (1 ≤ p)] (h : ℕ) (v : Vec h) (i : Coord h) :
    |v i| ≤ (upper p h v).1+(upper p h v).2 := by
  induction h with
  | zero =>
    have hi : i=() := Subsingleton.elim _ _
    subst i
    change |v ()| ≤ max (v ()) 0+max (-v ()) 0
    rw [abs_le]; constructor <;> linarith [le_max_left (v ()) 0,le_max_right (v ()) 0,le_max_left (-v ()) 0,le_max_right (-v ()) 0]
  | succ h ih =>
    cases i with
    | inl u =>
      have hu : u=() := Subsingleton.elim _ _
      subst u
      have hh := join_root_bound (rootChildren h v).1
        (aggregate p ((rootChildren h v).2.mapRange (fun z => (upper p h z).1) (by simp)))
        (aggregate p ((rootChildren h v).2.mapRange (fun z => (upper p h z).2) (by simp)))
        (aggregate_nonneg _ _) (aggregate_nonneg _ _)
      exact hh
    | inr a =>
      have hh := ih ((rootChildren h v).2 a.1) a.2
      have hb := upper_child_bound p h v a.1
      exact hh.trans (add_le_add hb.1 hb.2)

def nu (p : ℝ≥0∞) (h : ℕ) (v : Vec h) : ℝ := (upper p h v).1+(upper p h v).2
lemma nu_nonneg (p : ℝ≥0∞) (h : ℕ) (v : Vec h) : 0 ≤ nu p h v :=
  add_nonneg (upper_nonneg p h v).1 (upper_nonneg p h v).2
@[simp] lemma nu_zero (p : ℝ≥0∞) (h : ℕ) : nu p h 0=0 := by simp [nu]
lemma nu_add (p : ℝ≥0∞) [Fact (1 ≤ p)] (h : ℕ) (v w : Vec h) :
    nu p h (v+w) ≤ nu p h v+nu p h w := by
  have ha := upper_add p h v w
  dsimp [nu]; linarith [ha.1,ha.2]
lemma nu_neg (p : ℝ≥0∞) (h : ℕ) (v : Vec h) : nu p h (-v)=nu p h v := by
  simp only [nu,upper_neg]; ring
lemma nu_smul (p : ℝ≥0∞) [Fact (1 ≤ p)] (h : ℕ) (v : Vec h) (t : ℝ) :
    nu p h (t • v)=|t| * nu p h v := by
  rcases le_total 0 t with ht|ht
  · simp only [nu,upper_smul_nonneg p h v t ht,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,abs_of_nonneg ht,mul_add]
  · have he : t • v=-((-t) • v) := by module
    rw [he,nu_neg]
    simp only [nu,upper_smul_nonneg p h v (-t) (neg_nonneg.mpr ht),Prod.smul_fst,Prod.smul_snd,smul_eq_mul,abs_of_nonpos ht,mul_add]
lemma nu_eq_zero (p : ℝ≥0∞) [Fact (1 ≤ p)] (h : ℕ) (v : Vec h) (hv : nu p h v=0) : v=0 := by
  ext i
  have hi := upper_coordinate_bound p h v i
  change |v i| ≤ nu p h v at hi
  rw [hv] at hi
  exact abs_nonpos_iff.mp hi

def nuSeminorm (p : ℝ≥0∞) [Fact (1 ≤ p)] (h : ℕ) : Seminorm ℝ (Vec h) where
  toFun := nu p h
  map_zero' := nu_zero p h
  add_le' := nu_add p h
  neg' := nu_neg p h
  smul' := fun t v => by simpa only [Real.norm_eq_abs] using nu_smul p h v t

/-- Finite disjoint forest, one positive-height rooted tree per component. -/
abbrev ForestCoord := Σ h : ℕ,Coord (h+1)
abbrev ForestVec := ForestCoord →₀ ℝ
def components : ForestVec ≃ₗ[ℝ] (Π₀ h : ℕ,Vec (h+1)) := sigmaFinsuppLequivDFinsupp ℝ
@[simp] lemma components_apply (v : ForestVec) (h : ℕ) (i : Coord (h+1)) : components v h i=v ⟨h,i⟩ := rfl

def componentValues (f : ∀ h,ZeroHom (Vec (h+1)) ℝ) (v : ForestVec) : ℕ →₀ ℝ :=
  (DFinsupp.mapRange (fun h => f h) (fun h => (f h).map_zero) (components v)).toFinsupp
@[simp] lemma componentValues_apply (f : ∀ h,ZeroHom (Vec (h+1)) ℝ) (v : ForestVec) (h : ℕ) :
    componentValues f v h=f h (components v h) := rfl
@[simp] lemma componentValues_zero (f : ∀ h,ZeroHom (Vec (h+1)) ℝ) : componentValues f 0=0 := by ext h; simp

def exponent (h : ℕ) : ℝ≥0∞ := 1+(h+1:ℝ≥0∞)⁻¹
instance exponent_ge_one (h : ℕ) : Fact (1 ≤ exponent h) := ⟨le_add_of_nonneg_right bot_le⟩
def nuMap (h : ℕ) : ZeroHom (Vec (h+1)) ℝ := ⟨nu (exponent h) (h+1),nu_zero _ _⟩
def vectorNormValues (v : ForestVec) : ℕ →₀ ℝ := componentValues nuMap v
@[simp] lemma vectorNormValues_apply (v : ForestVec) (h : ℕ) : vectorNormValues v h=nu (exponent h) (h+1) (components v h) := rfl
@[simp] lemma vectorNormValues_zero : vectorNormValues 0=0 := componentValues_zero _
lemma vectorNormValues_nonneg (v : ForestVec) (h : ℕ) : 0 ≤ vectorNormValues v h := nu_nonneg _ _ _
lemma vectorNormValues_add (v w : ForestVec) (h : ℕ) : vectorNormValues (v+w) h ≤ (vectorNormValues v+vectorNormValues w) h := by
  simp only [vectorNormValues_apply,map_add,DFinsupp.add_apply,Finsupp.add_apply]
  exact nu_add _ _ _ _
lemma vectorNormValues_neg (v : ForestVec) : vectorNormValues (-v)=vectorNormValues v := by
  ext h
  simp only [vectorNormValues_apply,map_neg,DFinsupp.neg_apply]
  exact nu_neg _ _ _
lemma vectorNormValues_smul (t : ℝ) (v : ForestVec) : vectorNormValues (t • v)=|t| • vectorNormValues v := by
  ext h
  simp only [vectorNormValues_apply,map_smul,DFinsupp.smul_apply,Finsupp.smul_apply,smul_eq_mul]
  exact nu_smul _ _ _ _

/-- Exactly the outer Hilbert sum of the root-sum ν_h norms with p_h=1+1/h. -/
def vectorNorm (v : ForestVec) : ℝ := aggregate 2 (vectorNormValues v)
@[simp] lemma vectorNorm_zero : vectorNorm 0=0 := by simp [vectorNorm]
lemma vectorNorm_add (v w : ForestVec) : vectorNorm (v+w) ≤ vectorNorm v+vectorNorm w := by
  exact (aggregate_mono 2 _ _ (vectorNormValues_nonneg _) (vectorNormValues_add _ _)).trans (aggregate_add 2 _ _)
lemma vectorNorm_neg (v : ForestVec) : vectorNorm (-v)=vectorNorm v := by simp only [vectorNorm,vectorNormValues_neg]
lemma vectorNorm_smul (t : ℝ) (v : ForestVec) : vectorNorm (t • v)=|t| * vectorNorm v := by
  simp only [vectorNorm,vectorNormValues_smul,aggregate_smul,abs_abs]
lemma vectorNorm_coordinate (v : ForestVec) (i : ForestCoord) : |v i| ≤ vectorNorm v := by
  have hh := upper_coordinate_bound (exponent i.1) (i.1+1) (components v i.1) i.2
  have hb := coordinate_le_aggregate 2 (vectorNormValues v) i.1
  exact hh.trans ((le_abs_self _).trans hb)
def vectorSeminorm : Seminorm ℝ ForestVec where
  toFun := vectorNorm
  map_zero' := vectorNorm_zero
  add_le' := vectorNorm_add
  neg' := vectorNorm_neg
  smul' t v := by simpa only [Real.norm_eq_abs] using vectorNorm_smul t v

/-- Separate Euclidean root arrays for the joined (p=2) models. -/
def rootP (h : ℕ) : ZeroHom (Vec (h+1)) ℝ :=
  ⟨fun v => (upper 2 (h+1) v).1,by simp⟩
def rootQ (h : ℕ) : ZeroHom (Vec (h+1)) ℝ :=
  ⟨fun v => (upper 2 (h+1) v).2,by simp⟩
def forestP (v : ForestVec) : ℝ := aggregate 2 (componentValues rootP v)
def forestQ (v : ForestVec) : ℝ := aggregate 2 (componentValues rootQ v)
@[simp] lemma forestP_zero : forestP 0=0 := by simp [forestP]
@[simp] lemma forestQ_zero : forestQ 0=0 := by simp [forestQ]
lemma forestP_nonneg (v : ForestVec) : 0 ≤ forestP v := aggregate_nonneg _ _
lemma forestQ_nonneg (v : ForestVec) : 0 ≤ forestQ v := aggregate_nonneg _ _
lemma forestP_add (v w : ForestVec) : forestP (v+w) ≤ forestP v+forestP w := by
  refine (aggregate_mono 2 _ _ ?_ ?_).trans (aggregate_add 2 _ _)
  · intro h; exact (upper_nonneg _ _ _).1
  · intro h
    change (upper 2 (h+1) (components (v+w) h)).1 ≤ (upper 2 (h+1) (components v h)).1+(upper 2 (h+1) (components w h)).1
    rw [map_add,DFinsupp.add_apply]
    exact (upper_add _ _ _ _).1
lemma forestQ_add (v w : ForestVec) : forestQ (v+w) ≤ forestQ v+forestQ w := by
  refine (aggregate_mono 2 _ _ ?_ ?_).trans (aggregate_add 2 _ _)
  · intro h; exact (upper_nonneg _ _ _).2
  · intro h
    change (upper 2 (h+1) (components (v+w) h)).2 ≤ (upper 2 (h+1) (components v h)).2+(upper 2 (h+1) (components w h)).2
    rw [map_add,DFinsupp.add_apply]
    exact (upper_add _ _ _ _).2
lemma forestP_neg (v : ForestVec) : forestP (-v)=forestQ v := by
  unfold forestP forestQ
  congr 1
  ext h
  change (upper 2 (h+1) (components (-v) h)).1=(upper 2 (h+1) (components v h)).2
  rw [map_neg,DFinsupp.neg_apply,upper_neg]
lemma forestQ_neg (v : ForestVec) : forestQ (-v)=forestP v := by
  simpa only [neg_neg] using (forestP_neg (-v)).symm
lemma forestP_smul (t : ℝ) (ht : 0 ≤ t) (v : ForestVec) : forestP (t • v)=t*forestP v := by
  have he : componentValues rootP (t • v)=t • componentValues rootP v := by
    ext h
    change (upper 2 (h+1) (components (t • v) h)).1=t*(upper 2 (h+1) (components v h)).1
    rw [map_smul,DFinsupp.smul_apply,upper_smul_nonneg _ _ _ _ ht]; rfl
  simp only [forestP,he,aggregate_smul,abs_of_nonneg ht]
lemma forestQ_smul (t : ℝ) (ht : 0 ≤ t) (v : ForestVec) : forestQ (t • v)=t*forestQ v := by
  rw [← forestP_neg,← smul_neg,forestP_smul t ht,forestP_neg]
lemma forest_coordinate (v : ForestVec) (i : ForestCoord) : |v i| ≤ forestP v+forestQ v := by
  have hi := upper_coordinate_bound (2:ℝ≥0∞) (i.1+1) (components v i.1) i.2
  have hp := (le_abs_self ((upper 2 (i.1+1) (components v i.1)).1)).trans
    (coordinate_le_aggregate 2 (componentValues rootP v) i.1)
  have hq := (le_abs_self ((upper 2 (i.1+1) (components v i.1)).2)).trans
    (coordinate_le_aggregate 2 (componentValues rootQ v) i.1)
  exact hi.trans (add_le_add hp hq)

/-- Root-zero common-root norm. The new root coordinate is absent, not free. -/
def zeroNorm (v : ForestVec) : ℝ := max (forestP v) (forestQ v)
@[simp] lemma zeroNorm_zero : zeroNorm 0=0 := by simp [zeroNorm]
lemma zeroNorm_add (v w : ForestVec) : zeroNorm (v+w) ≤ zeroNorm v+zeroNorm w := by
  apply max_le
  · exact (forestP_add v w).trans (add_le_add (le_max_left _ _) (le_max_left _ _))
  · exact (forestQ_add v w).trans (add_le_add (le_max_right _ _) (le_max_right _ _))
lemma zeroNorm_neg (v : ForestVec) : zeroNorm (-v)=zeroNorm v := by simp only [zeroNorm,forestP_neg,forestQ_neg,max_comm]
lemma zeroNorm_smul (t : ℝ) (v : ForestVec) : zeroNorm (t • v)=|t| * zeroNorm v := by
  rcases le_total 0 t with ht|ht
  · simp only [zeroNorm,forestP_smul t ht,forestQ_smul t ht,abs_of_nonneg ht,mul_max_of_nonneg _ _ ht]
  · have he : t • v=-((-t) • v) := by module
    rw [he,zeroNorm_neg]
    simp only [zeroNorm,forestP_smul (-t) (neg_nonneg.mpr ht),forestQ_smul (-t) (neg_nonneg.mpr ht),abs_of_nonpos ht,mul_max_of_nonneg _ _ (neg_nonneg.mpr ht)]
lemma zeroNorm_coordinate (v : ForestVec) (i : ForestCoord) : |v i| ≤ 2*zeroNorm v := by
  have hi := forest_coordinate v i
  dsimp [zeroNorm]
  linarith [le_max_left (forestP v) (forestQ v),le_max_right (forestP v) (forestQ v)]
def zeroSeminorm : Seminorm ℝ ForestVec where
  toFun := zeroNorm
  map_zero' := zeroNorm_zero
  add_le' := zeroNorm_add
  neg' := zeroNorm_neg
  smul' t v := by simpa only [Real.norm_eq_abs] using zeroNorm_smul t v

abbrev JoinedCoord := Unit ⊕ ForestCoord
abbrev JoinedVec := JoinedCoord →₀ ℝ
def joinedChildren : JoinedVec ≃ₗ[ℝ] ℝ × ForestVec :=
  (Finsupp.sumFinsuppLEquivProdFinsupp ℝ).trans
    ((Finsupp.uniqueLinearEquiv ℝ ℝ ()).prodCongr (LinearEquiv.refl ℝ ForestVec))
def joinedUpper (v : JoinedVec) : ℝ × ℝ :=
  join (joinedChildren v).1 (forestP (joinedChildren v).2) (forestQ (joinedChildren v).2)
/-- Free new-root sum, which is genuinely twice the common-root norm on root zero. -/
def joinedNorm (v : JoinedVec) : ℝ := (joinedUpper v).1+(joinedUpper v).2
@[simp] lemma joinedNorm_zero : joinedNorm 0=0 := by simp [joinedNorm,joinedUpper,join]
lemma joinedNorm_add (v w : JoinedVec) : joinedNorm (v+w) ≤ joinedNorm v+joinedNorm w := by
  let V := joinedChildren v
  let W := joinedChildren w
  have hm := join_mono (r := V.1+W.1) (forestP_add V.2 W.2) (forestQ_add V.2 W.2)
  have ha := join_add V.1 W.1 (forestP V.2) (forestQ V.2) (forestP W.2) (forestQ W.2)
  unfold joinedNorm joinedUpper
  rw [map_add]
  exact (add_le_add (hm.1.trans ha.1) (hm.2.trans ha.2)).trans_eq (by ring)
lemma joinedNorm_neg (v : JoinedVec) : joinedNorm (-v)=joinedNorm v := by
  simp only [joinedNorm,joinedUpper,join,map_neg,Prod.fst_neg,Prod.snd_neg,forestP_neg,forestQ_neg]
  simp only [sub_eq_add_neg,neg_neg,add_comm,max_comm]
lemma joinedNorm_smul_nonneg (t : ℝ) (ht : 0 ≤ t) (v : JoinedVec) : joinedNorm (t • v)=t*joinedNorm v := by
  simp only [joinedNorm,joinedUpper,map_smul,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,forestP_smul t ht,forestQ_smul t ht,join_smul t _ _ _ ht,mul_add]
lemma joinedNorm_smul (t : ℝ) (v : JoinedVec) : joinedNorm (t • v)=|t| * joinedNorm v := by
  rcases le_total 0 t with ht|ht
  · rw [joinedNorm_smul_nonneg t ht,abs_of_nonneg ht]
  · have he : t • v=-((-t) • v) := by module
    rw [he,joinedNorm_neg,joinedNorm_smul_nonneg (-t) (neg_nonneg.mpr ht),abs_of_nonpos ht]
lemma joinedNorm_coordinate (v : JoinedVec) (i : JoinedCoord) : |v i| ≤ joinedNorm v := by
  cases i with
  | inl u =>
    have hu : u=() := Subsingleton.elim _ _
    subst u
    exact join_root_bound _ _ _ (forestP_nonneg _) (forestQ_nonneg _)
  | inr i =>
    have hh := forest_coordinate (joinedChildren v).2 i
    exact hh.trans (add_le_add (le_max_left _ _) (le_max_right _ _))
lemma joinedNorm_root_zero (v : JoinedVec) (hv : (joinedChildren v).1=0) :
    joinedNorm v=2*zeroNorm (joinedChildren v).2 := by
  simp only [joinedNorm,joinedUpper,join,hv,zero_add,sub_zero,zeroNorm]
  ring
def joinedSeminorm : Seminorm ℝ JoinedVec where
  toFun := joinedNorm
  map_zero' := joinedNorm_zero
  add_le' := joinedNorm_add
  neg' := joinedNorm_neg
  smul' t v := by simpa only [Real.norm_eq_abs] using joinedNorm_smul t v

/-- Prefix ancestors, including both the root and the coordinate itself. -/
def ancestors : (h : ℕ) → Coord h → Finset (Coord h)
  | 0,_ => {()}
  | _+1,.inl _ => {.inl ()}
  | h+1,.inr (i,s) => insert (.inl ()) ((ancestors h s).image (fun t => .inr (i,t)))
lemma self_mem_ancestors (h : ℕ) (s : Coord h) : s ∈ ancestors h s := by
  induction h with
  | zero => simp [ancestors]
  | succ h ih =>
    cases s with
    | inl u => simp [ancestors]
    | inr a => exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a.2,ih _,rfl⟩)
lemma ancestor_trans (h : ℕ) {a b c : Coord h} (hab : a ∈ ancestors h b) (hbc : b ∈ ancestors h c) :
    a ∈ ancestors h c := by
  induction h with
  | zero => exact self_mem_ancestors _ _
  | succ h ih =>
    cases c with
    | inl u =>
      have hb : b=Sum.inl () := by simpa only [ancestors,Finset.mem_singleton] using hbc
      subst b
      simpa only [ancestors] using hab
    | inr k =>
      rcases Finset.mem_insert.mp hbc with hb|hb
      · subst b
        have ha : a=Sum.inl () := by simpa only [ancestors,Finset.mem_singleton] using hab
        subst a
        exact Finset.mem_insert_self _ _
      · obtain ⟨b',hb',rfl⟩ := Finset.mem_image.mp hb
        rcases Finset.mem_insert.mp hab with ha|ha
        · subst a; exact Finset.mem_insert_self _ _
        · obtain ⟨a',ha',rfl⟩ := Finset.mem_image.mp ha
          exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a',ih ha' hb',rfl⟩)

def forestAncestors (i : ForestCoord) : Finset ForestCoord :=
  (ancestors (i.1+1) i.2).image (Sigma.mk i.1)
lemma forest_self_mem (i : ForestCoord) : i ∈ forestAncestors i :=
  Finset.mem_image.mpr ⟨i.2,self_mem_ancestors _ _,rfl⟩
lemma forest_ancestor_trans {a b c : ForestCoord} (hab : a ∈ forestAncestors b) (hbc : b ∈ forestAncestors c) :
    a ∈ forestAncestors c := by
  obtain ⟨b',hb',rfl⟩ := Finset.mem_image.mp hbc
  obtain ⟨a',ha',rfl⟩ := Finset.mem_image.mp hab
  exact Finset.mem_image.mpr ⟨a',ancestor_trans _ ha' hb',rfl⟩

/-- Finite heads are componentwise ancestor closed; a used component includes
    its original root. There is no joined free root in this index type. -/
def ForestHead := {H : Finset ForestCoord // ∀ i ∈ H,forestAncestors i ⊆ H}
def forestHead (S : Finset ForestCoord) : ForestHead :=
  ⟨S.biUnion forestAncestors,by
    intro i hi j hj
    obtain ⟨k,hk,hi⟩ := Finset.mem_biUnion.mp hi
    exact Finset.mem_biUnion.mpr ⟨k,hk,forest_ancestor_trans hj hi⟩⟩
lemma forestHead_contains (S : Finset ForestCoord) : S ⊆ (forestHead S).val := by
  intro i hi
  exact Finset.mem_biUnion.mpr ⟨i,hi,forest_self_mem i⟩

def joinedAncestors : JoinedCoord → Finset JoinedCoord
  | .inl _ => {.inl ()}
  | .inr i => insert (.inl ()) ((forestAncestors i).image Sum.inr)
lemma joined_self_mem (i : JoinedCoord) : i ∈ joinedAncestors i := by
  cases i with
  | inl u => simp [joinedAncestors]
  | inr i => exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,forest_self_mem i,rfl⟩)
lemma joined_ancestor_trans {a b c : JoinedCoord} (hab : a ∈ joinedAncestors b) (hbc : b ∈ joinedAncestors c) :
    a ∈ joinedAncestors c := by
  cases c with
  | inl u =>
    have hb : b=Sum.inl () := by simpa only [joinedAncestors,Finset.mem_singleton] using hbc
    subst b
    simpa only [joinedAncestors] using hab
  | inr i =>
    rcases Finset.mem_insert.mp hbc with hb|hb
    · subst b
      have ha : a=Sum.inl () := by simpa only [joinedAncestors,Finset.mem_singleton] using hab
      subst a; exact Finset.mem_insert_self _ _
    · obtain ⟨b',hb',rfl⟩ := Finset.mem_image.mp hb
      rcases Finset.mem_insert.mp hab with ha|ha
      · subst a; exact Finset.mem_insert_self _ _
      · obtain ⟨a',ha',rfl⟩ := Finset.mem_image.mp ha
        exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a',forest_ancestor_trans ha' hb',rfl⟩)

/-- The joined root belongs to every allowed head, including otherwise empty heads. -/
def JoinedHead := {H : Finset JoinedCoord // Sum.inl () ∈ H ∧ ∀ i ∈ H,joinedAncestors i ⊆ H}
def joinedHead (S : Finset JoinedCoord) : JoinedHead :=
  ⟨insert (Sum.inl ()) (S.biUnion joinedAncestors),Finset.mem_insert_self _ _,by
    intro i hi j hj
    rcases Finset.mem_insert.mp hi with hi|hi
    · subst i
      have hj' : j=Sum.inl () := by simpa only [joinedAncestors,Finset.mem_singleton] using hj
      subst j; exact Finset.mem_insert_self _ _
    · obtain ⟨k,hk,hi⟩ := Finset.mem_biUnion.mp hi
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨k,hk,joined_ancestor_trans hj hi⟩)⟩
lemma joinedHead_contains (S : Finset JoinedCoord) : S ⊆ (joinedHead S).val := by
  intro i hi
  exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨i,hi,joined_self_mem i⟩)

/-- The dense-coordinate presentations of the three distinct recursive Banach
    spaces. Each space is the completion for its displayed, exact finite norm. -/
def vectorData : CoordinateCompletion.Data ForestCoord where
  seminorm := vectorSeminorm
  coordinate_bound i := ⟨1,fun v => by change |v i| ≤ 1*vectorNorm v; simpa using vectorNorm_coordinate v i⟩
def zeroData : CoordinateCompletion.Data ForestCoord where
  seminorm := zeroSeminorm
  coordinate_bound i := ⟨2,fun v => zeroNorm_coordinate v i⟩
def joinedData : CoordinateCompletion.Data JoinedCoord where
  seminorm := joinedSeminorm
  coordinate_bound i := ⟨1,fun v => by change |v i| ≤ 1*joinedNorm v; simpa using joinedNorm_coordinate v i⟩
abbrev VectorSpace := vectorData.Space
abbrev ZeroRootSpace := zeroData.Space
abbrev FreeRootSpace := joinedData.Space

def vectorHeads : Midpoint.Heads ForestHead VectorSpace :=
  vectorData.heads Subtype.val (fun S => ⟨forestHead S,forestHead_contains S⟩)
def zeroHeads : Midpoint.Heads ForestHead ZeroRootSpace :=
  zeroData.heads Subtype.val (fun S => ⟨forestHead S,forestHead_contains S⟩)
def freeHeads : Midpoint.Heads JoinedHead FreeRootSpace :=
  joinedData.heads Subtype.val (fun S => ⟨joinedHead S,joinedHead_contains S⟩)
lemma vectorHeads_commutes : vectorHeads.Commutes := vectorData.heads_commutes _ _
lemma zeroHeads_commutes : zeroHeads.Commutes := zeroData.heads_commutes _ _
lemma freeHeads_commutes : freeHeads.Commutes := joinedData.heads_commutes _ _

@[simp] lemma vector_norm_embedding (v : ForestVec) : ‖vectorData.embedding v‖=vectorNorm v :=
  vectorData.norm_embedding v
@[simp] lemma zero_norm_embedding (v : ForestVec) : ‖zeroData.embedding v‖=zeroNorm v :=
  zeroData.norm_embedding v
@[simp] lemma free_norm_embedding (v : JoinedVec) : ‖joinedData.embedding v‖=joinedNorm v :=
  joinedData.norm_embedding v

/-- The new-root coordinate vanishes on every pure tail for an allowed joined head. -/
lemma pure_tail_new_root (H : JoinedHead) {y : FreeRootSpace}
    (hy : freeHeads.projection H y=0) : joinedData.coordinate (Sum.inl ()) y=0 := by
  have hh := congrArg (joinedData.coordinate (Sum.inl ())) hy
  change joinedData.coordinate (Sum.inl ()) (joinedData.projection H.val y)=_ at hh
  simpa only [CoordinateCompletion.Data.coordinate_projection,ite_eq_left H.property.1,map_zero] using hh

/-- Root-zero identification retains the factor two; the root-max and root-sum
    models are not silently normalized into one another. -/
lemma free_root_zero_norm (v : JoinedVec) (hv : (joinedChildren v).1=0) :
    ‖joinedData.embedding v‖=2*‖zeroData.embedding (joinedChildren v).2‖ := by
  rw [free_norm_embedding,zero_norm_embedding]
  exact joinedNorm_root_zero v hv

end

open RecursiveApplications

theorem sixth_graph (hinput : SixthInput vectorHeads) {D s : ℝ} (k : ℕ)
    (f : Diamond.Vertex k → VectorSpace) (hf : Diamond.HasDistortion k f D s) :
    D⁻¹ ≤ (q6 D⁻¹)^k := sixth_depth vectorHeads hinput k f hf

theorem cubic_graph (hinput : CubicInput vectorHeads) {D s : ℝ} (k : ℕ)
    (f : Diamond.Vertex k → VectorSpace) (hf : Diamond.HasDistortion k f D s) :
    1 ≤ D*(theta D⁻¹)^k := cubic_depth vectorHeads hinput k f hf

theorem cubic_weak (hinput : CubicInput vectorHeads) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {x : VectorSpace} (z : ℕ → VectorSpace) (hz : Midpoint.WeaklyNull z)
    (hl : ∀ i,ε ≤ ‖z i‖) (hp : ∀ i,‖x+z i‖ ≤ 1) (hm : ∀ i,‖x-z i‖ ≤ 1) :
    ‖x‖ ≤ theta ε := cubic_weak_lens vectorHeads hinput hε hε1 z hz hl hp hm

theorem free_lens {γ : ℝ → ℝ → ℝ} (hinput : FreeRootInput freeHeads γ) {ε : ℝ}
    (hε : 0 < ε) (_hε2 : ε ≤ 2) :
    0 < sumEta γ ε ∧ sumEta γ ε < 1 ∧
      Diamond.UnitLensBound FreeRootSpace ε (1-sumEta γ ε) :=
  ⟨(sumEta_range freeHeads hinput hε).1,(sumEta_range freeHeads hinput hε).2,
    free_root_lens freeHeads freeHeads_commutes hinput hε⟩

theorem free_graph {γ : ℝ → ℝ → ℝ} (hinput : FreeRootInput freeHeads γ) {D s : ℝ} (k : ℕ)
    (f : Diamond.Vertex k → FreeRootSpace) (hf : Diamond.HasDistortion k f D s) :
    D⁻¹ ≤ (1-sumEta γ (2/D))^k := free_root_depth freeHeads freeHeads_commutes hinput k f hf

theorem zero_graph (hinput : ZeroRootInput zeroHeads) {D s : ℝ} (k : ℕ)
    (f : Diamond.Vertex k → ZeroRootSpace) (hf : Diamond.HasDistortion k f D s) :
    (k:ℝ) ≤ 4608*D^3*(1-D⁻¹) := zero_root_depth zeroHeads hinput k f hf
end RecursiveModel

end DiamondDistortion

end

end OAI
