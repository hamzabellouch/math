import OAI.NumberTheory.SingleFold.FiniteGeneration

namespace OAI

namespace SingleFold.AbstractRank

universe u v w

variable (A : Type u) [AddCommGroup A]

def doubleRange : AddSubgroup A := (nsmulAddMonoidHom (α:=A) 2).range

def doubleKernel : AddSubgroup A := (nsmulAddMonoidHom (α:=A) 2).ker

lemma mem_doubleRange (x : A) : x ∈ doubleRange A ↔ ∃ y, (2:ℕ) • y=x := Iff.rfl
lemma mem_doubleKernel (x : A) : x ∈ doubleKernel A ↔ (2:ℕ) • x=0 := Iff.rfl

lemma index_le_of_cover (F : Finset A) (hF : ∀ P, ∃ R ∈ F, ∃ Q, P=R+(2:ℕ) • Q) :
    (doubleRange A).index ≤ F.card := by
  have hs : Function.Surjective (fun R : F => (QuotientAddGroup.mk R.val : A ⧸ doubleRange A)) := by
    intro x
    obtain ⟨P,rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨R,hR,Q,hQ⟩ := hF P
    refine ⟨⟨R,hR⟩,?_⟩
    apply QuotientAddGroup.eq.mpr
    change -R+P ∈ doubleRange A
    refine ⟨Q,?_⟩
    simp only [nsmulAddMonoidHom_apply]
    rw [hQ]
    abel
  simpa [AddSubgroup.index, Nat.card_eq_fintype_card] using Nat.card_le_card_of_surjective _ hs

lemma doubleRange_prod (B : Type v) [AddCommGroup B] :
    doubleRange (A×B)=(doubleRange A).prod (doubleRange B) := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact ⟨⟨y.1,rfl⟩,⟨y.2,rfl⟩⟩
  · rintro ⟨⟨a,ha⟩,⟨b,hb⟩⟩
    exact ⟨(a,b),Prod.ext ha hb⟩

lemma doubleRange_pi (ι : Type v) :
    doubleRange (ι → A)=AddSubgroup.pi Set.univ (fun _ => doubleRange A) := by
  classical
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    intro i _
    exact ⟨y i,rfl⟩
  · intro h
    have hh : ∀ i, ∃ y, (2:ℕ) • y=x i := fun i => h i (Set.mem_univ i)
    choose y hy using hh
    exact ⟨y,funext hy⟩

lemma doubleRange_int : doubleRange ℤ = AddSubgroup.zmultiples (2:ℤ) := by
  exact Int.range_nsmulAddMonoidHom 2

lemma free_index (n : ℕ) : (doubleRange (Fin n → ℤ)).index = 2^n := by
  rw [doubleRange_pi,AddSubgroup.index_pi]
  simp [doubleRange_int,Int.index_zmultiples]

lemma finite_index_eq_kernel [Finite A] : (doubleRange A).index = Nat.card (doubleKernel A) :=
  AddSubgroup.index_range

variable {A}

lemma doubleRange_map {B : Type v} [AddCommGroup B] (f : A ≃+ B) :
    (doubleRange A).map f.toAddMonoidHom=doubleRange B := by
  ext x
  constructor
  · rintro ⟨y,⟨z,hz⟩,rfl⟩
    refine ⟨f z,?_⟩
    change (2:ℕ) • f z=f y
    rw [←map_nsmul,f.injective.eq_iff]
    exact hz
  · rintro ⟨y,rfl⟩
    refine ⟨(2:ℕ) • f.symm y,⟨f.symm y,rfl⟩,?_⟩
    simp

lemma doubleRange_index_equiv {B : Type v} [AddCommGroup B] (f : A ≃+ B) :
    (doubleRange A).index=(doubleRange B).index := by
  rw [←doubleRange_map f]
  exact (AddSubgroup.index_map_equiv _ f).symm

noncomputable def doubleKernel_equiv {B : Type v} [AddCommGroup B] (f : A ≃+ B) :
    doubleKernel A ≃ doubleKernel B where
  toFun x := ⟨f x,by
    change (2:ℕ) • f x=0
    rw [←map_nsmul]
    have hx := x.property
    change (2:ℕ) • (x:A)=0 at hx
    rw [hx,map_zero]⟩
  invFun x := ⟨f.symm x,by
    change (2:ℕ) • f.symm x=0
    rw [←map_nsmul]
    have hx := x.property
    change (2:ℕ) • (x:B)=0 at hx
    rw [hx,map_zero]⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp

noncomputable def doubleKernel_free_prod_equiv (ι : Type v) (T : Type w) [AddCommGroup T] :
    doubleKernel ((ι → ℤ)×T) ≃ doubleKernel T where
  toFun x := ⟨x.val.2,congrArg Prod.snd x.property⟩
  invFun x := ⟨(0,x.val), Prod.ext (by simp) x.property⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · ext i
      have hh := congrArg (fun a : (ι → ℤ)×T => a.1 i) x.property
      change (2:ℕ) • x.val.1 i=0 at hh
      simp only [nsmul_eq_mul] at hh
      change 0=x.val.1 i
      omega
    · rfl
  right_inv x := rfl

lemma index_rank_formula {T : Type w} [AddCommGroup T] [Finite T] (n : ℕ)
    (f : A ≃+ (Fin n → ℤ)×T) :
    (doubleRange A).index = 2^n * Nat.card (doubleKernel A) := by
  rw [doubleRange_index_equiv f,doubleRange_prod,AddSubgroup.index_prod,free_index,
    finite_index_eq_kernel]
  congr 1
  exact (Nat.card_congr ((doubleKernel_equiv f).trans
    (doubleKernel_free_prod_equiv (Fin n) T))).symm

theorem exists_rank_le_one [AddGroup.FG A]
    (hindex : (doubleRange A).index ≤ 8) (hker : 4 ≤ Nat.card (doubleKernel A)) :
    ∃ (n : ℕ) (T : Type) (_ : AddCommGroup T) (_ : Finite T),
      n ≤ 1 ∧ Nonempty (A ≃+ (Fin n → ℤ) × T) := by
  classical
  obtain ⟨n,ι,hi,p,hp,e,⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod A
  let T := DirectSum ι (fun i => ZMod (p i ^ e i))
  have hp0 : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  let : Finite T := Finite.of_equiv (∀ i, ZMod (p i ^ e i)) DFinsupp.equivFunOnFintype.symm
  let g : A ≃+ (Fin n → ℤ)×T := f.trans
    ((Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n)).toAddEquiv.prodCongr (AddEquiv.refl T))
  have heq := index_rank_formula n g
  have hpow : 2^n ≤ 2 := by nlinarith
  have hn : n ≤ 1 := by
    by_contra h
    have hh : 2^2 ≤ 2^n := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at hh
    omega
  exact ⟨n,T,inferInstance,inferInstance,hn,⟨g⟩⟩

end SingleFold.AbstractRank

namespace SingleFold.CurveRank
open Descent WeierstrassCurve.Affine.Point

noncomputable instance : Finite (AbstractRank.doubleKernel E.Point) := by
  let S : Set E.Point := {P | CurveHeight.canonicalHeight P ≤ 0}
  have hS : S.Finite := Northcott.finite_le (h := CurveHeight.canonicalHeight) 0
  let f : AbstractRank.doubleKernel E.Point → S := fun P => ⟨P.val,by
    have hh := CurveHeight.canonicalHeight_nsmul P.val 2
    have hp := P.property
    change (2:ℕ) • P.val=0 at hp
    rw [hp,CurveHeight.canonicalHeight_zero] at hh
    norm_num at hh
    change CurveHeight.canonicalHeight P.val ≤ 0
    linarith⟩
  have : Finite S := hS.to_subtype
  exact Finite.of_injective f (by intro x y h; exact Subtype.ext (congrArg (fun z : S => z.val) h))

def Tm5 : E.Point := some (-5) 0 (E.equation_iff_nonsingular.mp (by
  norm_num [WeierstrassCurve.Affine.equation_iff]))

lemma double_torsion (P : E.Point) (hP : P=0 ∨ P=T0 ∨ P=T5 ∨ P=Tm5) :
    (2:ℕ) • P=0 := by
  rcases hP with rfl|rfl|rfl|rfl
  · simp
  all_goals
    rw [two_smul]
    simp only [T0,T5,Tm5]
    apply add_self_of_Y_eq
    norm_num [WeierstrassCurve.Affine.negY]

lemma four_le_doubleKernel : 4 ≤ Nat.card (AbstractRank.doubleKernel E.Point) := by
  let f : Fin 4 → AbstractRank.doubleKernel E.Point := fun i =>
    ⟨![0,T0,T5,Tm5] i,by
      apply double_torsion
      fin_cases i <;> simp⟩
  have hf : Function.Injective f := by
    intro i j h
    have hh := congrArg (fun x : AbstractRank.doubleKernel E.Point => x.val) h
    change ![0,T0,T5,Tm5] i = ![0,T0,T5,Tm5] j at hh
    fin_cases i <;> fin_cases j <;>
      simp_all [T0,T5,Tm5]
    all_goals norm_num at hh
  simpa using Nat.card_le_card_of_injective f hf

theorem rank_at_most_one :
    ∃ (n : ℕ) (T : Type) (_ : AddCommGroup T) (_ : Finite T),
      n ≤ 1 ∧ Nonempty (E.Point ≃+ (Fin n → ℤ) × T) := by
  apply AbstractRank.exists_rank_le_one
  · exact (AbstractRank.index_le_of_cover E.Point representatives representatives_cover).trans
      representatives_card
  · exact four_le_doubleKernel

end SingleFold.CurveRank

namespace SingleFold.ValuationRank
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

abbrev E : WeierstrassCurve.Affine ℚ := ⟨0,0,0,-25,0⟩
instance : E.IsElliptic := by
  constructor
  norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

lemma equation {x y : ℚ} (h : E.Nonsingular x y) : y^2=x^3-25*x := by
  simpa [WeierstrassCurve.Affine.equation_iff,sub_eq_add_neg] using h.1

lemma val_add_eq {p : ℕ} [Fact p.Prime] {x y : ℚ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hval : padicValRat p x ≠ padicValRat p y) :
    padicValRat p (x+y) = min (padicValRat p x) (padicValRat p y) := by
  apply padicValRat.add_eq_min _ hx hy hval
  intro h
  apply hval
  have he : x = -y := by linarith
  simp [he]

lemma val_25 : padicValRat 2 25=0 := by
  change padicValRat 2 (25:ℕ)=0
  rw [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd (by decide)]
  rfl
lemma val_4 : padicValRat 2 4=2 := by
  rw [show (4:ℚ)=2^2 by norm_num,padicValRat.pow]
  have hh : padicValRat 2 2=1 := padicValRat.self (by norm_num : 1 < (2:ℕ))
  simp [hh]

lemma val_sq_add {x : ℚ} (hx : padicValRat 2 x < 0) :
    padicValRat 2 (x^2+25)=2*padicValRat 2 x := by
  have hxn : x ≠ 0 := by intro he; simp [he] at hx
  have hh := val_add_eq (p:=2) (pow_ne_zero 2 hxn) (by norm_num : (25:ℚ) ≠ 0)
    (by rw [padicValRat.pow,val_25]; norm_num; omega)
  rw [padicValRat.pow,val_25,min_eq_left] at hh
  · simpa using hh
  · norm_num; omega

lemma val_sq_sub {x : ℚ} (hx : padicValRat 2 x < 0) :
    padicValRat 2 (x^2-25)=2*padicValRat 2 x := by
  have hxn : x ≠ 0 := by intro he; simp [he] at hx
  have hh := val_add_eq (p:=2) (pow_ne_zero 2 hxn) (by norm_num : (-25:ℚ) ≠ 0)
    (by rw [padicValRat.pow,padicValRat.neg,val_25]; norm_num; omega)
  rw [padicValRat.pow,padicValRat.neg,val_25,min_eq_left] at hh
  · simpa [sub_eq_add_neg] using hh
  · norm_num; omega

lemma duplication {x y : ℚ} (h : E.Nonsingular x y) (hy : y ≠ 0) :
    ∃ h' : E.Nonsingular ((x^2+25)^2/(4*y^2)) (E.addY x x y (E.slope x x y y)),
      (2:ℕ) • some x y h = some ((x^2+25)^2/(4*y^2)) (E.addY x x y (E.slope x x y y)) h' := by
  have hy' : y ≠ E.negY x y := by simpa [WeierstrassCurve.Affine.negY] using (show y ≠ -y by intro hh; apply hy; linarith)
  have hs : E.slope x x y y = (3*x^2-25)/(2*y) := by
    rw [slope_of_Y_ne rfl hy']
    simp
    congr 1 <;> ring
  have hx' : E.addX x x (E.slope x x y y) = (x^2+25)^2/(4*y^2) := by
    rw [WeierstrassCurve.Affine.addX,hs]
    dsimp
    field_simp
    have he := equation h
    linear_combination -32*x*he
  rw [two_smul,add_self_of_Y_ne hy']
  have he := E.nonsingular_add h h (by simpa using hy')
  rw [hx'] at he
  exact ⟨he,by simp only [hx']⟩

lemma double_val {x y : ℚ} (h : E.Nonsingular x y) (hx : padicValRat 2 x < 0) :
    ∃ (x' y' : ℚ) (h' : E.Nonsingular x' y'),
      (2:ℕ) • some x y h = some x' y' h' ∧
      padicValRat 2 x'=padicValRat 2 x-2 := by
  have hxn : x ≠ 0 := by intro he; simp [he] at hx
  have hs := val_sq_sub hx
  have hsn : x^2-25 ≠ 0 := by intro he; rw [he,padicValRat.zero] at hs; omega
  have he : y^2=x*(x^2-25) := by nlinarith only [equation h]
  have hyn : y ≠ 0 := by
    intro he'
    apply mul_ne_zero hxn hsn
    rw [←he,he']
    norm_num
  obtain ⟨h',hh⟩ := duplication h hyn
  refine ⟨_,_,h',hh,?_⟩
  have hp : x^2+25 ≠ 0 := by nlinarith [sq_nonneg x]
  rw [padicValRat.div (pow_ne_zero 2 hp) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hyn)),
    padicValRat.pow,padicValRat.mul (by norm_num) (pow_ne_zero 2 hyn),val_4,
    he,padicValRat.mul hxn hsn,val_sq_add hx,hs]
  ring

noncomputable def vx : E.Point → ℤ
  | .zero => 0
  | .some x _ _ => padicValRat 2 x

lemma vx_double (P : E.Point) (h : vx P < 0) : vx ((2:ℕ) • P)=vx P-2 := by
  cases P with
  | zero => simp [vx] at h
  | some x y hp =>
    obtain ⟨x',y',h',hh,hv⟩ := double_val hp h
    rw [hh]
    exact hv

def G : E.Point := some (25/4) (75/8) (E.equation_iff_nonsingular.mp (by
  norm_num [WeierstrassCurve.Affine.equation_iff]))

lemma vx_G : vx G = -2 := by
  change padicValRat 2 (25/4)= -2
  rw [padicValRat.div (by norm_num) (by norm_num),val_25,val_4]
  norm_num

lemma vx_dyadic (n : ℕ) : vx ((2^n:ℕ) • G)= -2-2*(n:ℤ) := by
  induction n with
  | zero => simpa using vx_G
  | succ n hn =>
    rw [pow_succ',mul_smul,vx_double _ (by rw [hn]; omega),hn]
    push_cast
    ring

lemma dyadic_injective : Function.Injective (fun n : ℕ => (2^n:ℕ) • G) := by
  intro n m h
  have hh := congrArg vx h
  rw [vx_dyadic,vx_dyadic] at hh
  omega

lemma G_nontorsion : ¬IsOfFinAddOrder G := by
  intro h
  have hf : (Set.range (fun n : ℕ => (2^n:ℕ) • G)).Finite :=
    h.finite_multiples.subset (by rintro _ ⟨n,rfl⟩; exact ⟨2^n,rfl⟩)
  exact (Set.infinite_range_of_injective dyadic_injective) hf

end SingleFold.ValuationRank

namespace SingleFold.CurveRank
open Descent

theorem rank_one : ∃ (T : Type) (_ : AddCommGroup T) (_ : Finite T),
    Nonempty (E.Point ≃+ (Fin 1 → ℤ) × T) := by
  obtain ⟨n,T,hT,hfin,hn,⟨f⟩⟩ := rank_at_most_one
  rcases (show n=0 ∨ n=1 by omega) with rfl|rfl
  · let : Finite E.Point := Finite.of_equiv ((Fin 0 → ℤ)×T) f.symm.toEquiv
    exact False.elim (ValuationRank.G_nontorsion (isOfFinAddOrder_of_finite _))
  · exact ⟨T,hT,hfin,⟨f⟩⟩

end SingleFold.CurveRank

end OAI
