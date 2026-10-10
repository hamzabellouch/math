import Mathlib
import OAI.Geometry.BallPacking.DiskMaps.CubicAreaExhaustion

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology Manifold
open Set Function
variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_smooth_convex_selection {Y : Set P} (hY : IsClosed Y)
    (S : P → Set F) (hopen : ∀ v, IsOpen {y | v ∈ S y})
    (hconv : ∀ y ∈ Y, Convex ℝ (S y)) (hne : ∀ y ∈ Y, (S y).Nonempty) :
    ∃ c : P → F, ContDiff ℝ ∞ c ∧ ∀ y ∈ Y, c y ∈ S y := by
  classical
  choose v hv using fun y : Y => hne y y.property
  let U : Y → Set P := fun y => {x | v y ∈ S x}
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ,P) hY U
    (fun y => hopen (v y)) (by
      intro y hy
      exact mem_iUnion_of_mem ⟨y,hy⟩ (hv ⟨y,hy⟩))
  refine ⟨fun y => ∑ᶠ i, ρ i y • v i,?_,?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro y
    exact ρ.contDiffAt_finsum (fun _ _ => contDiffAt_const)
  · intro y hy
    apply ρ.finsum_smul_mem_convex hy _ (hconv y hy)
    intro i hi
    exact hρ i (subset_tsupport (ρ i) hi)


end

section
open Set Function

theorem exists_strict_interval_extension {a b l u L : ℝ}
    (hal : a < l) (hub : u < b) (hLu : u-l < L) (hLb : L < b-a) :
    ∃ c, a < c ∧ c+L < b ∧ c < l ∧ u < c+L := by
  have hh : max a (u-L) < min l (b-L) := by
    rw [max_lt_iff,lt_min_iff,lt_min_iff]
    constructor <;> constructor <;> linarith
  obtain ⟨c,hlo,hhi⟩ := exists_between hh
  exact ⟨c,(le_max_left _ _).trans_lt hlo,
    by linarith [(lt_of_lt_of_le hhi (min_le_right _ _))],
    hhi.trans_le (min_le_left _ _),
    by linarith [(lt_of_le_of_lt (le_max_right _ _) hlo)]⟩

theorem exists_strict_nested_intervals {n : ℕ} (a b L : Fin n → ℝ)
    (ha : Antitone a) (hb : Monotone b) (hL : StrictMono L)
    (hfit : ∀ i, L i < b i-a i) :
    ∃ c : Fin n → ℝ, (∀ i, a i < c i ∧ c i+L i < b i) ∧
      ∀ ⦃i j⦄, i < j → c j < c i ∧ c i+L i < c j+L j := by
  induction n with
  | zero => exact ⟨fun i => i.elim0,by simp,by simp⟩
  | succ n ih =>
    cases n with
    | zero =>
      refine ⟨fun i => (a i+b i-L i)/2,?_,?_⟩
      · intro i; have := hfit i; constructor <;> linarith
      · intro i j hij
        have : i = j := by omega
        exact (lt_irrefl _ (this ▸ hij)).elim
    | succ m =>
      obtain ⟨c,hc,hnest⟩ := ih (a ∘ Fin.castSucc) (b ∘ Fin.castSucc)
        (L ∘ Fin.castSucc) (ha.comp_monotone Fin.strictMono_castSucc.monotone)
        (hb.comp Fin.strictMono_castSucc.monotone) (hL.comp Fin.strictMono_castSucc)
        (fun i => hfit i.castSucc)
      let i₀ : Fin (m+1) := Fin.last m
      let j₀ : Fin (m+2) := Fin.last (m+1)
      have hij : i₀.castSucc < j₀ := Fin.castSucc_lt_last _
      obtain ⟨d,hd⟩ := exists_strict_interval_extension
        ((ha hij.le).trans_lt (hc i₀).1)
        ((hc i₀).2.trans_le (hb hij.le))
        (by simpa only [Function.comp_apply,add_sub_cancel_left] using hL hij)
        (hfit j₀)
      refine ⟨Fin.snoc c d,?_,?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [Fin.snoc_last] using And.intro hd.1 hd.2.1
        · simpa only [Fin.snoc_castSucc,Function.comp_apply] using hc j
      · intro i j hij'
        have hi : i ≠ Fin.last (m+1) := by
          intro hh
          subst i
          exact not_lt_of_ge (Fin.le_last _) hij'
        obtain ⟨i,rfl⟩ := Fin.eq_castSucc_of_ne_last hi
        revert hij'
        refine Fin.lastCases ?_ (fun j hj => ?_) j
        · intro _
          simp only [Fin.snoc_castSucc,Fin.snoc_last]
          rcases lt_or_eq_of_le (Fin.le_last i) with hi | hi
          · have hh := hnest hi
            exact ⟨hd.2.2.1.trans hh.1,hh.2.trans hd.2.2.2⟩
          · subst i
            exact hd.2.2
        · simpa only [Fin.snoc_castSucc,Function.comp_apply] using
            hnest (show i < j from hj)


end

section
open scoped ContDiff Topology
open Set Function

variable {n : ℕ}

def StrictNestedStarts (L c : Fin n → ℝ) : Prop :=
  ∀ ⦃i j : Fin n⦄, i < j → c j < c i ∧ c i+L i < c j+L j

def IntervalPlacements (L : Fin n → ℝ) (V : Fin n → Set ℝ) : Set (Fin n → ℝ) :=
  {c | (∀ i, c i ∈ V i ∧ c i+L i ∈ V i) ∧ StrictNestedStarts L c}

theorem intervalPlacements_convex (L : Fin n → ℝ) (V : Fin n → Set ℝ)
    (hV : ∀ i, Convex ℝ (V i)) : Convex ℝ (IntervalPlacements L V) := by
  intro c hc d hd α β hα hβ hab
  refine ⟨?_,?_⟩
  · intro i
    have he : (α • c+β • d) i+L i = α*(c i+L i)+β*(d i+L i) := by
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      have he := congrArg (fun t : ℝ => t*L i) hab
      nlinarith only [he]
    constructor
    · exact hV i (hc.1 i).1 (hd.1 i).1 hα hβ hab
    · rw [he]
      exact hV i (hc.1 i).2 (hd.1 i).2 hα hβ hab
  · intro i j hij
    let A : (Fin n → ℝ) →ₗ[ℝ] ℝ := (LinearMap.proj j : (Fin n → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj i
    let B : (Fin n → ℝ) →ₗ[ℝ] ℝ := (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj j
    have ha : A c < 0 := sub_neg.mpr (hc.2 hij).1
    have hb : A d < 0 := sub_neg.mpr (hd.2 hij).1
    have ha' : B c < L j-L i := by change c i-c j < _; linarith [(hc.2 hij).2]
    have hb' : B d < L j-L i := by change d i-d j < _; linarith [(hd.2 hij).2]
    have hh := (convex_halfSpace_lt A.isLinear 0) ha hb hα hβ hab
    have hh' := (convex_halfSpace_lt B.isLinear (L j-L i)) ha' hb' hα hβ hab
    change (α • c+β • d) j-(α • c+β • d) i < 0 at hh
    change (α • c+β • d) i-(α • c+β • d) j < L j-L i at hh'
    exact ⟨sub_neg.mp hh,by linarith⟩

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_smooth_nested_intervals {Y : Set P} (hY : IsClosed Y)
    (L : Fin n → ℝ) (hL : StrictMono L) (V : P → Fin n → Set ℝ)
    (hopen : ∀ i t, IsOpen {y | t ∈ V y i})
    (hconv : ∀ y ∈ Y, ∀ i, Convex ℝ (V y i))
    (hroom : ∀ y ∈ Y, ∃ a b : Fin n → ℝ, Antitone a ∧ Monotone b ∧
      (∀ i, L i < b i-a i) ∧ ∀ i, Ioo (a i) (b i) ⊆ V y i)
    (hpos : ∀ i, 0 < L i) :
    ∃ c : P → (Fin n → ℝ), ContDiff ℝ ∞ c ∧
      ∀ y ∈ Y, (∀ i, Icc (c y i) (c y i+L i) ⊆ V y i) ∧
        StrictNestedStarts L (c y) := by
  have hsopen (c : Fin n → ℝ) : IsOpen {y | c ∈ IntervalPlacements L (V y)} := by
    change IsOpen {y | (∀ i, c i ∈ V y i ∧ c i+L i ∈ V y i) ∧ StrictNestedStarts L c}
    by_cases hn : StrictNestedStarts L c
    · simp only [hn,and_true,ofPred_forall,ofPred_and]
      exact isOpen_iInter_of_finite (fun i => (hopen i (c i)).inter (hopen i (c i+L i)))
    · simp only [hn,and_false,ofPred_false,isOpen_empty]
  have hsne (y : P) (hy : y ∈ Y) : (IntervalPlacements L (V y)).Nonempty := by
    obtain ⟨a,b,ha,hb,hfit,hsub⟩ := hroom y hy
    obtain ⟨c,hc,hn⟩ := exists_strict_nested_intervals a b L ha hb hL hfit
    refine ⟨c,?_,hn⟩
    intro i
    have hLi := hpos i
    exact ⟨hsub i ⟨(hc i).1,by linarith [(hc i).2]⟩,
      hsub i ⟨by linarith [(hc i).1],(hc i).2⟩⟩
  obtain ⟨c,hc,hmem⟩ := exists_smooth_convex_selection hY
    (fun y => IntervalPlacements L (V y)) hsopen
    (fun y hy => intervalPlacements_convex L (V y) (hconv y hy)) hsne
  refine ⟨c,hc,?_⟩
  intro y hy
  refine ⟨?_,(hmem y hy).2⟩
  intro i
  exact (hconv y hy i).ordConnected.out ((hmem y hy).1 i).1 ((hmem y hy).1 i).2


end

section
open scoped ContDiff Topology
open Set Function
variable {P : Type*} [TopologicalSpace P]

def RoundedMargins {n : ℕ} (C : P → Fin n → ℝ) (L w : Fin n → ℝ)
    (V : P → Fin n → Set ℝ) (q s : ℝ) (y : P) : Prop :=
  0 < s ∧
  (∀ i, C y i-s*L i/2 ∈ V y i ∧ C y i+s*L i/2 ∈ V y i) ∧
  ∀ ⦃i j⦄, i < j →
    C y j-q*s*L j/2 < C y i-s*L i/2 ∧
    C y i+s*L i/2 < C y j+q*s*L j/2 ∧ w i < q*w j

theorem roundedMargins_open {n : ℕ} (C : P → Fin n → ℝ) (hC : Continuous C)
    (L w : Fin n → ℝ) (V : P → Fin n → Set ℝ)
    (hV : ∀ i, IsOpen {p : P × ℝ | p.2 ∈ V p.1 i}) :
    IsOpen {p : Plane × P | RoundedMargins C L w V p.1.1 p.1.2 p.2} := by
  have hlo (i : Fin n) : IsOpen {p : Plane × P | C p.2 i-p.1.2*L i/2 ∈ V p.2 i} :=
    (hV i).preimage (continuous_snd.prodMk
      (((continuous_apply i).comp (hC.comp continuous_snd)).sub
        ((continuous_fst.snd.mul continuous_const).div_const 2)))
  have hhi (i : Fin n) : IsOpen {p : Plane × P | C p.2 i+p.1.2*L i/2 ∈ V p.2 i} :=
    (hV i).preimage (continuous_snd.prodMk
      (((continuous_apply i).comp (hC.comp continuous_snd)).add
        ((continuous_fst.snd.mul continuous_const).div_const 2)))
  have hpair (i j : Fin n) : IsOpen {p : Plane × P | i < j →
      C p.2 j-p.1.1*p.1.2*L j/2 < C p.2 i-p.1.2*L i/2 ∧
      C p.2 i+p.1.2*L i/2 < C p.2 j+p.1.1*p.1.2*L j/2 ∧ w i < p.1.1*w j} := by
    by_cases hij : i < j
    · simp only [hij,true_implies,ofPred_and]
      exact (isOpen_lt (by fun_prop) (by fun_prop)).inter
        ((isOpen_lt (by fun_prop) (by fun_prop)).inter (isOpen_lt (by fun_prop) (by fun_prop)))
    · simp only [hij,false_implies,ofPred_true,isOpen_univ]
  change IsOpen {p : Plane × P | 0 < p.1.2 ∧
    (∀ i, C p.2 i-p.1.2*L i/2 ∈ V p.2 i ∧ C p.2 i+p.1.2*L i/2 ∈ V p.2 i) ∧
    ∀ i j, i < j → _}
  simp only [ofPred_and,ofPred_forall]
  exact (isOpen_lt continuous_const continuous_fst.snd).inter
    ((isOpen_iInter_of_finite (fun i => (hlo i).inter (hhi i))).inter
      (isOpen_iInter_of_finite (fun i => isOpen_iInter_of_finite (fun j => by
        simpa only [ofPred_forall,ofPred_and] using hpair i j))))

theorem exists_exact_area_rounded_margins {n : ℕ} {Y : Set P} (hY : IsCompact Y)
    (c : P → Fin n → ℝ) (hc : Continuous c) (L w : Fin n → ℝ)
    (hw : StrictMono w) (V : P → Fin n → Set ℝ)
    (hV : ∀ i, IsOpen {p : P × ℝ | p.2 ∈ V p.1 i})
    (hplace : ∀ y ∈ Y, (∀ i, c y i ∈ V y i ∧ c y i+L i ∈ V y i) ∧
      StrictNestedStarts L (c y)) :
    ∃ q k : ℝ, 0 < q ∧ q < 1 ∧ 0 < k ∧
      Icc (-q) q ×ˢ Icc (-q) q ⊆ squeezedDisk k ∧ 0 < squeezedArea k ∧
      ∀ y ∈ Y, RoundedMargins (fun y i => c y i+L i/2) L w V q (4/squeezedArea k) y := by
  let C : P → Fin n → ℝ := fun y i => c y i+L i/2
  have hC : Continuous C := by
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp hc).add continuous_const
  apply exists_rounded_square_with_control hY continuous_id
    (roundedMargins_open C hC L w V hV)
  intro y hy
  change RoundedMargins C L w V 1 1 y
  refine ⟨by norm_num,?_,?_⟩
  · intro i
    simpa only [C,one_mul,add_sub_cancel_right,add_assoc,add_halves] using (hplace y hy).1 i
  · intro i j hij
    dsimp [C]
    simp only [one_mul,add_sub_cancel_right,add_assoc,add_halves]
    exact ⟨((hplace y hy).2 hij).1,((hplace y hy).2 hij).2,hw hij⟩


end

section
open scoped ContDiff Topology BigOperators
open Set Function

theorem exists_thin_rectangle_placement {m : ℕ} (h : Fin m → ℝ)
    (hh : ∀ i, 0 < h i) (hmono : StrictMono h) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (L w c : Fin m → ℝ), (∀ i, 0 < L i) ∧ (∀ i, 0 < w i ∧ w i < 1) ∧
      StrictMono w ∧ (∀ i, L i*w i = h i) ∧ StrictNestedStarts L c ∧
      ∀ i, c i ∈ Ioo 0 (h i+δ/2) ∧ c i+L i ∈ Ioo 0 (h i+δ/2) := by
  let B : ℝ := 1+∑ i, h i
  have hB : 1 ≤ B := by
    have hs : 0 ≤ ∑ i, h i := Finset.sum_nonneg (fun i _ => (hh i).le)
    dsimp [B]; linarith
  have hiB (i : Fin m) : h i < B := by
    have hi := Finset.single_le_sum (s := Finset.univ) (fun j _ => (hh j).le) (Finset.mem_univ i)
    dsimp [B]; linarith
  let ε := min (δ/8) (1/4)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hεδ : ε ≤ δ/8 := min_le_left _ _
  have hε1 : ε ≤ 1/4 := min_le_right _ _
  let β := ε/(2*B)
  have hd : 0 < 2*B := by linarith
  have hβ : 0 < β := div_pos hε hd
  have hβ1 : β < 1 := by apply (div_lt_one hd).mpr; linarith
  have hB0 : B ≠ 0 := ne_of_gt (by linarith)
  have hβB : β*B = ε/2 := by dsimp [β]; field_simp [hB0]
  have hsmall (i : Fin m) : β*h i < ε := by
    have he := mul_lt_mul_of_pos_left (hiB i) hβ
    rw [hβB] at he
    linarith
  let L i := h i+ε
  let w i := h i/(h i+ε)
  let c i := ε-β*h i
  have hL i : 0 < L i := add_pos (hh i) hε
  have hw i : 0 < w i ∧ w i < 1 :=
    ⟨div_pos (hh i) (hL i),(div_lt_one (hL i)).mpr (by dsimp [L]; linarith)⟩
  refine ⟨L,w,c,hL,hw,?_,?_,?_,?_⟩
  · intro i j hij
    apply (div_lt_div_iff₀ (hL i) (hL j)).mpr
    dsimp [L]
    have he := mul_lt_mul_of_pos_right (hmono hij) hε
    nlinarith
  · intro i
    dsimp [L,w]
    field_simp [show h i+ε ≠ 0 from (hL i).ne']
  · intro i j hij
    dsimp [c,L]
    have he := hmono hij
    have he1 := mul_lt_mul_of_pos_left he hβ
    have he2 := mul_lt_mul_of_pos_left he (sub_pos.mpr hβ1)
    constructor <;> nlinarith
  · intro i
    have hc : 0 < c i := sub_pos.mpr (hsmall i)
    have hcε : c i < ε := by dsimp [c]; nlinarith [mul_pos hβ (hh i)]
    have hlower : 0 < c i+L i := add_pos hc (hL i)
    have hupper : c i+L i < h i+δ/2 := by dsimp [L]; linarith
    exact ⟨⟨hc,(lt_add_of_pos_right (c i) (hL i)).trans hupper⟩,hlower,hupper⟩


end

section
open scoped ContDiff Topology
open Set Function MeasureTheory

def box (c : Plane) (a b : ℝ) : Set Plane :=
  Icc (c.1-a) (c.1+a) ×ˢ Icc (c.2-b) (c.2+b)

def openBox (c : Plane) (a b : ℝ) : Set Plane :=
  Ioo (c.1-a) (c.1+a) ×ˢ Ioo (c.2-b) (c.2+b)

def roundedMap (k : ℝ) (c : Plane) (a b : ℝ) (x : Plane) : Plane :=
  affineRectangle c a b (squareSqueeze k x)

def roundedBox (k : ℝ) (c : Plane) (a b : ℝ) : Set Plane :=
  roundedMap k c a b '' closedRoundDisk 1

theorem affineRectangle_injective {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (c : Plane) :
    Injective (affineRectangle c a b) := by
  intro x y he
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  exact Prod.ext (mul_left_cancel₀ ha (add_left_cancel h1))
    (mul_left_cancel₀ hb (add_left_cancel h2))

theorem affineRectangle_smooth (c : Plane) (a b : ℝ) :
    ContDiff ℝ ∞ (affineRectangle c a b) :=
  contDiff_const.add (diagonalScale a b).contDiff

theorem roundedMap_smooth (k : ℝ) (c : Plane) (a b : ℝ) :
    ContDiff ℝ ∞ (roundedMap k c a b) :=
  (affineRectangle_smooth c a b).comp (squareSqueeze_smooth k)

theorem roundedMap_injective {k a b : ℝ} (hk : k ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (c : Plane) : Injective (roundedMap k c a b) :=
  (affineRectangle_injective ha hb c).comp (squareSqueeze_injective hk)

theorem affineRectangle_fderiv (c : Plane) (a b : ℝ) (x : Plane) :
    fderiv ℝ (affineRectangle c a b) x = diagonalScale a b := by
  exact ((diagonalScale a b).hasFDerivAt.const_add c).fderiv

theorem roundedMap_det {k a b : ℝ} (c : Plane) (x : Plane) :
    (fderiv ℝ (roundedMap k c a b) x).det = a*b*(fderiv ℝ (squareSqueeze k) x).det := by
  change (fderiv ℝ (affineRectangle c a b ∘ squareSqueeze k) x).det = _
  rw [fderiv_comp x ((affineRectangle_smooth c a b).differentiable (by simp) _)
    ((squareSqueeze_smooth k).differentiable (by simp) _),affineRectangle_fderiv,
    ContinuousLinearMap.det,ContinuousLinearMap.toLinearMap_comp,LinearMap.det_comp]
  change (diagonalScale a b).det * _ = _
  rw [diagonalScale_det]

theorem roundedMap_det_pos {k a b : ℝ} (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (c : Plane) (x : Plane) : 0 < (fderiv ℝ (roundedMap k c a b) x).det := by
  rw [roundedMap_det]
  exact mul_pos (mul_pos ha hb) (squareSqueeze_det_pos hk x)

theorem roundedMap_mem_openBox {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (k : ℝ) (c : Plane) (x : Plane) : roundedMap k c a b x ∈ openBox c a b := by
  have hx1 := Real.neg_one_lt_tanh (k*x.1)
  have hx2 := Real.tanh_lt_one (k*x.1)
  have hy1 := Real.neg_one_lt_tanh (k*x.2)
  have hy2 := Real.tanh_lt_one (k*x.2)
  change (c.1-a < c.1+a*Real.tanh (k*x.1) ∧ c.1+a*Real.tanh (k*x.1) < c.1+a) ∧
    (c.2-b < c.2+b*Real.tanh (k*x.2) ∧ c.2+b*Real.tanh (k*x.2) < c.2+b)
  constructor <;> constructor <;> nlinarith

theorem box_subset_roundedBox {q k a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : Icc (-q) q ×ˢ Icc (-q) q ⊆ squeezedDisk k) (c : Plane) :
    box c (q*a) (q*b) ⊆ roundedBox k c a b := by
  intro x hx
  let z : Plane := ((x.1-c.1)/a,(x.2-c.2)/b)
  have hz : z ∈ Icc (-q) q ×ˢ Icc (-q) q := by
    change (-q ≤ (x.1-c.1)/a ∧ (x.1-c.1)/a ≤ q) ∧
      (-q ≤ (x.2-c.2)/b ∧ (x.2-c.2)/b ≤ q)
    constructor <;> constructor
    · apply (le_div_iff₀ ha).mpr; linarith [hx.1.1]
    · apply (div_le_iff₀ ha).mpr; linarith [hx.1.2]
    · apply (le_div_iff₀ hb).mpr; linarith [hx.2.1]
    · apply (div_le_iff₀ hb).mpr; linarith [hx.2.2]
  obtain ⟨u,hu,he⟩ := hs hz
  refine ⟨u,hu,?_⟩
  change affineRectangle c a b (squareSqueeze k u) = x
  rw [he]
  ext <;> simp [affineRectangle,z,mul_div_cancel₀ _ ha.ne',mul_div_cancel₀ _ hb.ne']

theorem openBox_subset_interior_roundedBox {q k a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : Icc (-q) q ×ˢ Icc (-q) q ⊆ squeezedDisk k) (c : Plane) :
    openBox c (q*a) (q*b) ⊆ interior (roundedBox k c a b) := by
  apply (isOpen_Ioo.prod isOpen_Ioo).subset_interior_iff.mpr
  exact (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self).trans
    (box_subset_roundedBox ha hb hs c)

theorem roundedBox_compact (k : ℝ) (c : Plane) (a b : ℝ) :
    IsCompact (roundedBox k c a b) :=
  (closedRoundDisk_isCompact 1).image (roundedMap_smooth k c a b).continuous

theorem roundedBox_volume {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (k : ℝ) (c : Plane) :
    (volume (roundedBox k c a b)).toReal = a*b*squeezedArea k := by
  change (volume ((affineRectangle c a b ∘ squareSqueeze k) '' closedRoundDisk 1)).toReal = _
  rw [image_comp]
  exact affineRectangle_squeezedArea ha hb c k


end

section
open scoped ContDiff Topology
open Set Function Filter
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable [FiniteDimensional ℝ E]

theorem isInvertible_of_det_ne_zero {A : E →L[ℝ] E} (hA : A.det ≠ 0) : A.IsInvertible :=
  ⟨(A.toLinearMap.equivOfDetNeZero hA).toContinuousLinearEquiv,rfl⟩

theorem smooth_map_nhds_eq {f : E → E} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (hd : (fderiv ℝ f x).det ≠ 0) : map f (𝓝 x) = 𝓝 (f x) := by
  obtain ⟨e,he⟩ := isInvertible_of_det_ne_zero hd
  have hs := hf.hasStrictFDerivAt (by simp)
  rw [← he] at hs
  exact hs.map_nhds_eq_of_equiv

theorem image_interior_subset_of_det_ne_zero {f : E → E} {S : Set E}
    (hf : ∀ x ∈ interior S, ContDiffAt ℝ ∞ f x)
    (hd : ∀ x ∈ interior S, (fderiv ℝ f x).det ≠ 0) :
    f '' interior S ⊆ interior (f '' S) := by
  rintro _ ⟨x,hx,rfl⟩
  apply mem_interior_iff_mem_nhds.mpr
  have hh := Filter.image_mem_map (m := f) (mem_interior_iff_mem_nhds.mp hx)
  rwa [smooth_map_nhds_eq (hf x hx) (hd x hx)] at hh

variable [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem det_fderiv_conjugate (e : E ≃L[ℝ] F) {f : F → F} {x : E}
    (hf : DifferentiableAt ℝ f (e x)) :
    (fderiv ℝ (fun x => e.symm (f (e x))) x).det = (fderiv ℝ f (e x)).det := by
  have hd := e.symm.hasFDerivAt.comp x (hf.hasFDerivAt.comp x e.hasFDerivAt)
  change (fderiv ℝ (e.symm ∘ f ∘ e) x).det = _
  rw [hd.fderiv]
  change LinearMap.det (e.symm.toLinearEquiv.toLinearMap ∘ₗ
    (fderiv ℝ f (e x)).toLinearMap ∘ₗ e.toLinearEquiv.toLinearMap) = _
  exact LinearMap.det_conj _ e.symm.toLinearEquiv


end

open scoped ContDiff Topology
open Set Function MeasureTheory

def FitsPolar (c : Plane) (a b : ℝ) : Prop :=
  0 < c.1-a ∧ c.1+a < 1 ∧ 0 < c.2-b ∧ c.2+b < 1

theorem openBox_subset_polar {c : Plane} {a b : ℝ} (hfit : FitsPolar c a b) :
    openBox c a b ⊆ areaPolarDomain := by
  intro x hx
  exact ⟨hfit.1.trans hx.1.1,hfit.2.2.1.trans hx.2.1,hx.2.2.trans hfit.2.2.2⟩

def polarRoundedMap (k : ℝ) (c : Plane) (a b : ℝ) (x : Plane) : Plane :=
  areaPolar (roundedMap k c a b x)

def polarRoundedDisk (k : ℝ) (c : Plane) (a b : ℝ) : Set Plane :=
  polarRoundedMap k c a b '' closedRoundDisk 1

theorem polarRoundedMap_injective {k a b : ℝ} (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (c : Plane) (hfit : FitsPolar c a b) : Injective (polarRoundedMap k c a b) := by
  intro x y he
  apply roundedMap_injective hk.ne' ha.ne' hb.ne' c
  exact areaPolar_injOn (openBox_subset_polar hfit (roundedMap_mem_openBox ha hb k c x))
    (openBox_subset_polar hfit (roundedMap_mem_openBox ha hb k c y)) he

theorem polarRoundedMap_smooth {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (k : ℝ) (c : Plane) (hfit : FitsPolar c a b) : ContDiff ℝ ∞ (polarRoundedMap k c a b) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact (areaPolar_smoothAt (openBox_subset_polar hfit (roundedMap_mem_openBox ha hb k c x)).1).comp x
    (roundedMap_smooth k c a b).contDiffAt

theorem polarRoundedMap_det {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (k : ℝ) (c : Plane) (hfit : FitsPolar c a b) (x : Plane) :
    (fderiv ℝ (polarRoundedMap k c a b) x).det = (fderiv ℝ (roundedMap k c a b) x).det := by
  have hp := (openBox_subset_polar hfit (roundedMap_mem_openBox ha hb k c x)).1
  change (fderiv ℝ (areaPolar ∘ roundedMap k c a b) x).det = _
  rw [fderiv_comp x ((areaPolar_smoothAt hp).differentiableAt (by simp))
    ((roundedMap_smooth k c a b).differentiable (by simp) _),
    ContinuousLinearMap.det,ContinuousLinearMap.toLinearMap_comp,LinearMap.det_comp]
  change (fderiv ℝ areaPolar (roundedMap k c a b x)).det * _ = _
  rw [areaPolar_det hp,one_mul]

theorem polarRoundedMap_det_pos {k a b : ℝ} (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (c : Plane) (hfit : FitsPolar c a b) (x : Plane) :
    0 < (fderiv ℝ (polarRoundedMap k c a b) x).det := by
  rw [polarRoundedMap_det ha hb k c hfit]
  exact roundedMap_det_pos hk ha hb c x

theorem polarRoundedMap_capacity {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (k : ℝ) (c : Plane) (hfit : FitsPolar c a b) (x : Plane) :
    Real.pi * radiusSq (polarRoundedMap k c a b x) = (roundedMap k c a b x).1 :=
  areaPolar_capacity (openBox_subset_polar hfit (roundedMap_mem_openBox ha hb k c x)).1.le

theorem polarRoundedDisk_volume {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (k : ℝ) (c : Plane) (hfit : FitsPolar c a b) :
    (volume (polarRoundedDisk k c a b)).toReal = a*b*squeezedArea k := by
  change (volume ((areaPolar ∘ roundedMap k c a b) '' closedRoundDisk 1)).toReal = _
  rw [image_comp]
  change (volume (areaPolar '' roundedBox k c a b)).toReal = _
  rw [areaPolar_image_volume (roundedBox_compact k c a b).measurableSet (by
    rintro z ⟨x,_,rfl⟩
    exact openBox_subset_polar hfit (roundedMap_mem_openBox ha hb k c x))]
  exact roundedBox_volume ha.le hb.le k c

theorem polarRoundedDisk_nested {k a b a' b' : ℝ} {c c' : Plane}
    (ha' : 0 < a') (hb' : 0 < b') (hfit' : FitsPolar c' a' b')
    (hnest : roundedBox k c a b ⊆ interior (roundedBox k c' a' b')) :
    polarRoundedDisk k c a b ⊆ interior (polarRoundedDisk k c' a' b') := by
  change (areaPolar ∘ roundedMap k c a b) '' closedRoundDisk 1 ⊆
    interior ((areaPolar ∘ roundedMap k c' a' b') '' closedRoundDisk 1)
  rw [image_comp,image_comp]
  apply (image_mono hnest).trans
  apply image_interior_subset_of_det_ne_zero
  · intro x hx
    obtain ⟨z,_,rfl⟩ := interior_subset hx
    exact areaPolar_smoothAt (openBox_subset_polar hfit' (roundedMap_mem_openBox ha' hb' k c' z)).1
  · intro x hx
    obtain ⟨z,_,rfl⟩ := interior_subset hx
    rw [areaPolar_det (openBox_subset_polar hfit' (roundedMap_mem_openBox ha' hb' k c' z)).1]
    norm_num

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem polarRoundedFamily_smoothOn {A : Set P} (_hA : IsOpen A)
    (C : P → Plane) (hC : ContDiff ℝ ∞ C) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (k : ℝ) (hfit : ∀ y ∈ A, FitsPolar (C y) a b) :
    ContDiffOn ℝ ∞ (fun p : P × Plane => polarRoundedMap k (C p.1) a b p.2) (A ×ˢ univ) := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  have hg : ContDiff ℝ ∞ (fun p : P × Plane => roundedMap k (C p.1) a b p.2) :=
    (hC.comp contDiff_fst).add
      ((diagonalScale a b).contDiff.comp ((squareSqueeze_smooth k).comp contDiff_snd))
  exact (areaPolar_smoothAt
    (openBox_subset_polar (hfit p.1 hp.1) (roundedMap_mem_openBox ha hb k (C p.1) p.2)).1).comp p hg.contDiffAt



end PackingSufficiencySupport.Hamiltonian
end

end OAI
