import Mathlib
import OAI.GroupTheory.FiniteType.FiberCoreMap

namespace OAI

noncomputable section
namespace SequentialColimit
section
open Set Topology
universe u v
variable (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
  (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]

abbrev Space := DirectLimit X f

def incl (i : ℕ) : C(X i,Space X f) :=
  ⟨fun x => ⟦⟨i,x⟩⟧,continuous_quotient_mk'.comp continuous_sigmaMk⟩

@[simp] lemma incl_map (i j : ℕ) (h : i ≤ j) (x : X i) :
    incl X f j (f i j h x) = incl X f i x := DirectLimit.mk_apply (f:=f) _ _ _ _

lemma incl_injective (hf : ∀ i j h, Function.Injective (f i j h)) (i : ℕ) :
    Function.Injective (incl X f i) := DirectLimit.mk_injective f hf i

def lift {Y : Type v} [TopologicalSpace Y] (g : ∀ i, C(X i,Y))
    (hg : ∀ i j h x, g i x = g j (f i j h x)) : C(Space X f,Y) :=
  ⟨DirectLimit.lift f (fun i => g i) hg,by
    apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    exact continuous_sigma (fun i => (g i).continuous)⟩

@[simp] lemma lift_incl {Y : Type v} [TopologicalSpace Y] (g : ∀ i, C(X i,Y))
    (hg : ∀ i j h x, g i x = g j (f i j h x)) (i : ℕ) (x : X i) :
    lift X f g hg (incl X f i x) = g i x := rfl

variable [∀ n, NormalSpace (X n)] (hc : ∀ i j h, IsClosedEmbedding (f i j h))

def extendOne (i : ℕ) (g : C(X i,ℝ)) : C(X (i+1),ℝ) :=
  (g.exists_extension_forall_mem_of_isClosedEmbedding (t:=univ)
    (fun _ => mem_univ _) (by simp) (hc i (i+1) (by omega))).choose

lemma extendOne_eq (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
    (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
    [∀ n, NormalSpace (X n)] (hc : ∀ i j h, IsClosedEmbedding (f i j h))
    (i : ℕ) (g : C(X i,ℝ)) (x : X i) :
    extendOne X f hc i g (f i (i+1) (by omega) x) = g x :=
  congrFun (g.exists_extension_forall_mem_of_isClosedEmbedding (t:=univ)
    (fun _ => mem_univ _) (by simp) (hc i (i+1) (by omega))).choose_spec.2 x

def extendTail (n : ℕ) (g : C(X n,ℝ)) : ∀ k, C(X (n+k),ℝ)
  | 0 => g
  | k+1 => extendOne X f hc (n+k) (extendTail n g k)

lemma extendTail_compat (n : ℕ) (g : C(X n,ℝ)) {i j : ℕ} (h : i ≤ j) (x : X (n+i)) :
    extendTail X f hc n g j (f (n+i) (n+j) (by omega) x) = extendTail X f hc n g i x := by
  induction j,h using Nat.le_induction with
  | base => rw [DirectedSystem.map_self']
  | succ j hj ih =>
    rw [show f (n+i) (n+(j+1)) (by omega) x =
      f (n+j) (n+j+1) (by omega) (f (n+i) (n+j) (by omega) x) from
        (DirectedSystem.map_map' f _ _ x).symm]
    exact (extendOne_eq X f hc _ _ _).trans ih

def extendFamily (n : ℕ) (g : C(X n,ℝ)) (i : ℕ) : C(X i,ℝ) :=
  (extendTail X f hc n g i).comp (f i (n+i) (by omega))

lemma extendFamily_compat (n : ℕ) (g : C(X n,ℝ)) (i j : ℕ) (h : i ≤ j) (x : X i) :
    extendFamily X f hc n g i x = extendFamily X f hc n g j (f i j h x) := by
  change extendTail X f hc n g i (f _ _ _ x) =
    extendTail X f hc n g j (f _ _ _ (f _ _ _ x))
  rw [DirectedSystem.map_map']
  rw [← extendTail_compat X f hc n g h (f i (n+i) (by omega) x),DirectedSystem.map_map']

def extend (n : ℕ) (g : C(X n,ℝ)) : C(Space X f,ℝ) :=
  lift X f (extendFamily X f hc n g) (extendFamily_compat X f hc n g)

lemma extend_eq (n : ℕ) (g : C(X n,ℝ)) (x : X n) :
    extend X f hc n g (incl X f n x) = g x := by
  change extendTail X f hc n g n (f n (n+n) (by omega) x) = g x
  exact extendTail_compat X f hc n g (i:=0) (by omega) x

variable [∀ n, T2Space (X n)]

include hc in

theorem hausdorff : T2Space (Space X f) := by
  constructor
  intro x y hxy
  obtain ⟨n,a,b,rfl,rfl⟩ := DirectLimit.exists_eq_mk₂ f x y
  have hab : a ≠ b := by intro he; subst b; exact hxy rfl
  obtain ⟨g,hga,hgb,-⟩ := exists_continuous_zero_one_of_isClosed
    (s:={a}) (t:={b}) isClosed_singleton isClosed_singleton (by simpa using hab)
  apply separated_by_continuous (extend X f hc n g).continuous
  change extend X f hc n g (incl X f n a) ≠ extend X f hc n g (incl X f n b)
  rw [extend_eq,extend_eq,hga (by simp),hgb (by simp)]
  norm_num

include hc in
lemma incl_isClosedEmbedding [∀ n, CompactSpace (X n)] (i : ℕ) :
    IsClosedEmbedding (incl X f i) := by
  let := hausdorff X f hc
  exact (incl X f i).continuous.isClosedEmbedding (incl_injective X f (fun i j h => (hc i j h).injective) i)

end

open Set Topology
universe u v
variable (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
  (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]

lemma isOpen_iff_stages (U : Set (Space X f)) :
    IsOpen U ↔ ∀ i, IsOpen (incl X f i ⁻¹' U) := by
  rw [← isQuotientMap_quotient_mk'.isCoinducing.isOpen_preimage,isOpen_sigma_iff]
  rfl

lemma continuousOn_of_stages {Y : Type v} [TopologicalSpace Y]
    (g : Space X f → Y) (U : Set (Space X f)) (hU : IsOpen U)
    (hg : ∀ i, ContinuousOn (g ∘ incl X f i) (incl X f i ⁻¹' U)) : ContinuousOn g U := by
  apply (continuousOn_open_iff hU).mpr
  intro V hV
  apply (isOpen_iff_stages X f _).mpr
  intro i
  exact (hg i).isOpen_inter_preimage (hU.preimage (incl X f i).continuous) hV

end SequentialColimit

namespace SequentialCore
open Set Topology
universe u v w
variable (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
  (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
  {ι : Type v} {Q : Type w} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  (U : ι → ∀ n, Set (X n)) (pot : ι → ∀ n, X n → Q)
  (hU : ∀ a i j (h : i ≤ j) x, x ∈ U a i ↔ f i j h x ∈ U a j)
  (hpot : ∀ a i j (h : i ≤ j) x, pot a j (f i j h x) = pot a i x)

def baseSet (a : ι) : Set (SequentialColimit.Space X f) :=
  fun x => DirectLimit.lift f (fun i x => x ∈ U a i)
    (fun i j h x => propext (hU a i j h x)) x

def potential (a : ι) : SequentialColimit.Space X f → Q :=
  DirectLimit.lift f (pot a) (fun i j h x => (hpot a i j h x).symm)

@[simp] lemma mem_baseSet_incl (a : ι) (n : ℕ) (x : X n) :
    SequentialColimit.incl X f n x ∈ baseSet X f U hU a ↔ x ∈ U a n := Iff.rfl

@[simp] lemma potential_incl (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
    (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
    {ι : Type v} {Q : Type w} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (pot : ι → ∀ n, X n → Q)
    (hpot : ∀ a i j (h : i ≤ j) x, pot a j (f i j h x) = pot a i x)
    (a : ι) (n : ℕ) (x : X n) :
    potential X f pot hpot a (SequentialColimit.incl X f n x) = pot a n x := rfl

include hU in
lemma baseSet_open (hop : ∀ a n, IsOpen (U a n)) (a : ι) :
    IsOpen (baseSet X f U hU a) :=
  (SequentialColimit.isOpen_iff_stages X f _).mpr (hop a)

include hU in
lemma baseSet_cover (hcov : ∀ n (x : X n), ∃ a, x ∈ U a n)
    (x : SequentialColimit.Space X f) : ∃ a, x ∈ baseSet X f U hU a := by
  obtain ⟨n,x,rfl⟩ := DirectLimit.exists_eq_mk f x
  exact hcov n x

variable (hop : ∀ a n, IsOpen (U a n))
  (hcov : ∀ n (x : X n), ∃ a, x ∈ U a n)
  (hcont : ∀ a b n, ContinuousOn (fun x => pot b n x * (pot a n x)⁻¹) (U a n ∩ U b n))

include hop hcont in
lemma continuousOn_transition (a b : ι) :
    ContinuousOn (fun z : SequentialColimit.Space X f × Q =>
      potential X f pot hpot b z.1 * (potential X f pot hpot a z.1)⁻¹ * z.2)
      ((baseSet X f U hU a ∩ baseSet X f U hU b) ×ˢ univ) := by
  have hc : ContinuousOn (fun x => potential X f pot hpot b x * (potential X f pot hpot a x)⁻¹)
      (baseSet X f U hU a ∩ baseSet X f U hU b) := by
    apply SequentialColimit.continuousOn_of_stages X f
    · exact (baseSet_open X f U hU hop a).inter (baseSet_open X f U hU hop b)
    · exact fun n => hcont a b n
  exact (hc.comp continuous_fst.continuousOn (fun _ hz => hz.1)).mul continuous_snd.continuousOn

noncomputable def core : FiberBundleCore ι (SequentialColimit.Space X f) Q where
  baseSet := baseSet X f U hU
  isOpen_baseSet := baseSet_open X f U hU hop
  indexAt x := (baseSet_cover X f U hU hcov x).choose
  mem_baseSet_at x := (baseSet_cover X f U hU hcov x).choose_spec
  coordChange a b x q := potential X f pot hpot b x * (potential X f pot hpot a x)⁻¹ * q
  coordChange_self := by intros; simp
  continuousOn_coordChange := continuousOn_transition X f U pot hU hpot hop hcont
  coordChange_comp := by intros; group

lemma core_covering [DiscreteTopology Q] :
    IsCoveringMap (core X f U pot hU hpot hop hcov hcont).proj := FiberBundle.isCoveringMap

lemma core_surjective : Function.Surjective (core X f U pot hU hpot hop hcov hcont).proj :=
  fun x => ⟨⟨x,(1:Q)⟩,rfl⟩

end SequentialCore

namespace SequentialCoreTower
section
open Set Topology
universe u v w
variable (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
  (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
  (I : ℕ → Type v) (δ : ∀ i j, i ≤ j → I i ↪ I j)
  [DirectedSystem I (δ · · ·)]
  {Q : Type w} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  (Z : ∀ n, FiberBundleCore (I n) (X n) Q)
  (pot : ∀ n, I n → X n → Q)
  (hBase : ∀ i j (h : i ≤ j) a x,
    x ∈ (Z i).baseSet a ↔ f i j h x ∈ (Z j).baseSet (δ i j h a))
  (hPot : ∀ i j (h : i ≤ j) a x,
    pot j (δ i j h a) (f i j h x) = pot i a x)
  (hCoord : ∀ n a b x q, (Z n).coordChange a b x q = pot n b x * (pot n a x)⁻¹ * q)

abbrev Index := Σ i, I i

def stageSet (a : Index I) (n : ℕ) : Set (X n) :=
  (f n (max a.1 n) (le_max_right _ _)) ⁻¹'
    (Z (max a.1 n)).baseSet (δ a.1 (max a.1 n) (le_max_left _ _) a.2)

def stagePot (a : Index I) (n : ℕ) (x : X n) : Q :=
  pot (max a.1 n) (δ a.1 (max a.1 n) (le_max_left _ _) a.2)
    (f n (max a.1 n) (le_max_right _ _) x)

lemma stageSet_common (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
    (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
    (I : ℕ → Type v) (δ : ∀ i j, i ≤ j → I i ↪ I j)
    [DirectedSystem I (δ · · ·)]
    {Q : Type w} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (Z : ∀ n, FiberBundleCore (I n) (X n) Q)
    (hBase : ∀ i j (h : i ≤ j) a x,
      x ∈ (Z i).baseSet a ↔ f i j h x ∈ (Z j).baseSet (δ i j h a))
    (a : Index I) (n k : ℕ) (hi : a.1 ≤ k) (hn : n ≤ k) (x : X n) :
    x ∈ stageSet X f I δ Z a n ↔
      f n k hn x ∈ (Z k).baseSet (δ a.1 k hi a.2) := by
  change f n (max a.1 n) _ x ∈ (Z (max a.1 n)).baseSet _ ↔ _
  rw [hBase (max a.1 n) k (max_le hi hn),DirectedSystem.map_map',DirectedSystem.map_map']

lemma stagePot_common (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
    (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
    (I : ℕ → Type v) (δ : ∀ i j, i ≤ j → I i ↪ I j)
    [DirectedSystem I (δ · · ·)]
    {Q : Type w} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (pot : ∀ n, I n → X n → Q)
    (hPot : ∀ i j (h : i ≤ j) a x,
      pot j (δ i j h a) (f i j h x) = pot i a x)
    (a : Index I) (n k : ℕ) (hi : a.1 ≤ k) (hn : n ≤ k) (x : X n) :
    stagePot X f I δ pot a n x = pot k (δ a.1 k hi a.2) (f n k hn x) := by
  unfold stagePot
  rw [← hPot (max a.1 n) k (max_le hi hn),DirectedSystem.map_map',DirectedSystem.map_map']

include hBase in
lemma stageSet_compat (a : Index I) (i j : ℕ) (h : i ≤ j) (x : X i) :
    x ∈ stageSet X f I δ Z a i ↔ f i j h x ∈ stageSet X f I δ Z a j := by
  rw [stageSet_common X f I δ Z hBase a i (max a.1 j) (le_max_left _ _) (by omega)]
  change _ ↔ f j (max a.1 j) _ (f i j h x) ∈
    (Z (max a.1 j)).baseSet (δ a.1 (max a.1 j) (le_max_left _ _) a.2)
  rw [DirectedSystem.map_map']

include hPot in
lemma stagePot_compat (a : Index I) (i j : ℕ) (h : i ≤ j) (x : X i) :
    stagePot X f I δ pot a j (f i j h x) = stagePot X f I δ pot a i x := by
  rw [stagePot_common X f I δ pot hPot a i (max a.1 j) (le_max_left _ _) (by omega)]
  unfold stagePot
  rw [DirectedSystem.map_map']

lemma stageSet_open (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
    (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
    (I : ℕ → Type v) (δ : ∀ i j, i ≤ j → I i ↪ I j)
    [DirectedSystem I (δ · · ·)]
    {Q : Type w} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (Z : ∀ n, FiberBundleCore (I n) (X n) Q)
    (a : Index I) (n : ℕ) : IsOpen (stageSet X f I δ Z a n) :=
  ((Z _).isOpen_baseSet _).preimage (f _ _ _).continuous

include hBase in
lemma stageSet_cover (n : ℕ) (x : X n) : ∃ a, x ∈ stageSet X f I δ Z a n := by
  refine ⟨⟨n,(Z n).indexAt x⟩,?_⟩
  apply (stageSet_common X f I δ Z hBase _ n n (le_refl _) (le_refl _) x).mpr
  simpa only [DirectedSystem.map_self'] using (Z n).mem_baseSet_at x

include hBase hPot hCoord in
lemma transition_cont (a b : Index I) (n : ℕ) :
    ContinuousOn (fun x => stagePot X f I δ pot b n x *
      (stagePot X f I δ pot a n x)⁻¹)
      (stageSet X f I δ Z a n ∩ stageSet X f I δ Z b n) := by
  let k := max (max a.1 b.1) n
  have ha : a.1 ≤ k := by dsimp [k]; omega
  have hb : b.1 ≤ k := by dsimp [k]; omega
  have hn : n ≤ k := le_max_right _ _
  have hc := ((Z k).continuousOn_coordChange (δ _ _ ha a.2) (δ _ _ hb b.2)).comp
    ((f n k hn).continuous.prodMk continuous_const).continuousOn
    (s := stageSet X f I δ Z a n ∩ stageSet X f I δ Z b n) (t :=
      ((Z k).baseSet (δ _ _ ha a.2) ∩ (Z k).baseSet (δ _ _ hb b.2)) ×ˢ univ)
    (fun x hx => ⟨⟨(stageSet_common X f I δ Z hBase a n k ha hn x).mp hx.1,
      (stageSet_common X f I δ Z hBase b n k hb hn x).mp hx.2⟩,mem_univ (1:Q)⟩)
  apply hc.congr
  intro x hx
  dsimp [Function.comp_def]
  rw [hCoord,mul_one,stagePot_common X f I δ pot hPot a n k ha hn x,
    stagePot_common X f I δ pot hPot b n k hb hn x]

noncomputable def core : FiberBundleCore (Index I) (SequentialColimit.Space X f) Q :=
  SequentialCore.core X f (stageSet X f I δ Z) (stagePot X f I δ pot)
    (stageSet_compat X f I δ Z hBase) (stagePot_compat X f I δ pot hPot)
    (stageSet_open X f I δ Z) (stageSet_cover X f I δ Z hBase)
    (transition_cont X f I δ Z pot hBase hPot hCoord)

lemma core_covering [DiscreteTopology Q] :
    IsCoveringMap (core X f I δ Z pot hBase hPot hCoord).proj := FiberBundle.isCoveringMap

end

open Set Topology
variable (X : ℕ → Type) [∀ n, TopologicalSpace (X n)]
  (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
  (I : ℕ → Type) (δ : ∀ i j, i ≤ j → I i ↪ I j)
  [DirectedSystem I (δ · · ·)]
  {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  (Z : ∀ n, FiberBundleCore (I n) (X n) Q)
  (pot : ∀ n, I n → X n → Q)
  (hBase : ∀ i j (h : i ≤ j) a x,
    x ∈ (Z i).baseSet a ↔ f i j h x ∈ (Z j).baseSet (δ i j h a))
  (hPot : ∀ i j (h : i ≤ j) a x,
    pot j (δ i j h a) (f i j h x) = pot i a x)
  (hCoord : ∀ n a b x q, (Z n).coordChange a b x q = pot n b x * (pot n a x)⁻¹ * q)

lemma baseSet_incl (n : ℕ) (a : I n) (x : X n) :
    SequentialColimit.incl X f n x ∈ (core X f I δ Z pot hBase hPot hCoord).baseSet ⟨n,a⟩ ↔
      x ∈ (Z n).baseSet a := by
  change x ∈ stageSet X f I δ Z ⟨n,a⟩ n ↔ _
  rw [stageSet_common X f I δ Z hBase ⟨n,a⟩ n n (le_refl _) (le_refl _)]
  simp only [DirectedSystem.map_self']

lemma coordChange_incl (n : ℕ) (a b : I n) (x : X n) (q : Q) :
    (core X f I δ Z pot hBase hPot hCoord).coordChange ⟨n,a⟩ ⟨n,b⟩
      (SequentialColimit.incl X f n x) q = (Z n).coordChange a b x q := by
  change stagePot X f I δ pot ⟨n,b⟩ n x * (stagePot X f I δ pot ⟨n,a⟩ n x)⁻¹ * q = _
  rw [stagePot_common X f I δ pot hPot ⟨n,a⟩ n n (le_refl _) (le_refl _),
    stagePot_common X f I δ pot hPot ⟨n,b⟩ n n (le_refl _) (le_refl _)]
  simp only [DirectedSystem.map_self',hCoord]

noncomputable def coverIncl (n : ℕ) :
    C((Z n).TotalSpace,(core X f I δ Z pot hBase hPot hCoord).TotalSpace) :=
  FiberCoreMap.continuousMap (Z n) (core X f I δ Z pot hBase hPot hCoord)
    (SequentialColimit.incl X f n) (fun a => ⟨n,a⟩)
    (fun a x hx => (baseSet_incl X f I δ Z pot hBase hPot hCoord n a x).mpr hx)
    (fun a b x _ q => coordChange_incl X f I δ Z pot hBase hPot hCoord n a b x q)

@[simp] lemma coverIncl_proj (n : ℕ) (e : (Z n).TotalSpace) :
    (core X f I δ Z pot hBase hPot hCoord).proj (coverIncl X f I δ Z pot hBase hPot hCoord n e) =
      SequentialColimit.incl X f n ((Z n).proj e) := rfl

lemma coverIncl_range (n : ℕ) :
    range (coverIncl X f I δ Z pot hBase hPot hCoord n) =
      (core X f I δ Z pot hBase hPot hCoord).proj ⁻¹' range (SequentialColimit.incl X f n) := by
  ext e
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨(Z n).proj a,rfl⟩
  · rintro ⟨x,hx⟩
    obtain ⟨a,ha⟩ := (FiberCoreMap.fiber_bijective (Z n) (core X f I δ Z pot hBase hPot hCoord)
      (SequentialColimit.incl X f n) (fun a => ⟨n,a⟩)
      (fun a x hx => (baseSet_incl X f I δ Z pot hBase hPot hCoord n a x).mpr hx)
      (fun a b x _ q => coordChange_incl X f I δ Z pot hBase hPot hCoord n a b x q) x).2
      ⟨e,hx.symm⟩
    exact ⟨a.1,congrArg Subtype.val ha⟩

variable [∀ n, T2Space (X n)] [∀ n, NormalSpace (X n)] [∀ n, CompactSpace (X n)]
  (hf : ∀ i j h, IsClosedEmbedding (f i j h))

include hf in
lemma coverIncl_isClosedEmbedding (n : ℕ) :
    IsClosedEmbedding (coverIncl X f I δ Z pot hBase hPot hCoord n) := by
  refine ⟨FiberCoreMap.isEmbedding (Z n) (core X f I δ Z pot hBase hPot hCoord)
    (SequentialColimit.incl X f n) (fun a => ⟨n,a⟩)
    (fun a x hx => (baseSet_incl X f I δ Z pot hBase hPot hCoord n a x).mpr hx)
    (fun a b x _ q => coordChange_incl X f I δ Z pot hBase hPot hCoord n a b x q)
    (SequentialColimit.incl_isClosedEmbedding X f hf n).isEmbedding,?_⟩
  rw [coverIncl_range]
  exact (SequentialColimit.incl_isClosedEmbedding X f hf n).isClosed_range.preimage
    (core X f I δ Z pot hBase hPot hCoord).continuous_proj

end SequentialCoreTower

end

end OAI
