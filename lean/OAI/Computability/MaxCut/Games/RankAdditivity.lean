import Mathlib
import OAI.Computability.MaxCut.Games.Deletion
import OAI.Computability.MaxCut.Games.MatrixFourier

namespace OAI

/-!
# Rank-additive pairs of linear maps

The rank-additive selector in Appendix A.1 has a concrete geometric meaning:
the two image spaces are disjoint and the two kernels span the domain. These
lemmas apply over any field and arbitrary finite dimensions, in particular
over `ZMod 2` with the second map equal to `Y + X`.
-/

namespace MaxCutGames.Appendix.RankAdditivity

open Module LinearMap

variable {K W V : Type*} [Field K] [AddCommGroup W] [AddCommGroup V]
  [Module K W] [Module K V]

/-- Disjoint images prevent cancellation between the two map values. -/
theorem ker_add_of_disjoint (f g : W →ₗ[K] V)
    (h : Disjoint (LinearMap.range f) (LinearMap.range g)) :
    LinearMap.ker (f + g) = LinearMap.ker f ⊓ LinearMap.ker g := by
  ext w
  constructor
  · intro hw
    have hsum : f w + g w = 0 := hw
    have hf : f w = 0 := by
      apply Submodule.disjoint_def.mp h (f w)
      · exact ⟨w, rfl⟩
      · exact ⟨-w, by simpa only [map_neg] using (eq_neg_of_add_eq_zero_left hsum).symm⟩
    have hg : g w = 0 := by simpa only [hf, zero_add] using hsum
    exact ⟨hf, hg⟩
  · rintro ⟨hf, hg⟩
    change f w + g w = 0
    change f w = 0 at hf
    change g w = 0 at hg
    rw [hf, hg, add_zero]

variable [FiniteDimensional K W] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
/-- The exact rank-additivity criterion used to define `X ⪯ Y` in Appendix A.1. -/
theorem finrank_add_eq_iff (f g : W →ₗ[K] V) :
    finrank K (LinearMap.range (f + g)) =
        finrank K (LinearMap.range f) + finrank K (LinearMap.range g) ↔
      Disjoint (LinearMap.range f) (LinearMap.range g) ∧
        LinearMap.ker f ⊔ LinearMap.ker g = ⊤ := by
  have hf := f.finrank_range_add_finrank_ker
  have hg := g.finrank_range_add_finrank_ker
  have hfg := (f + g).finrank_range_add_finrank_ker
  have hker := (LinearMap.ker f).finrank_sup_add_finrank_inf_eq (LinearMap.ker g)
  constructor
  · intro hrank
    have hle := Submodule.finrank_mono (LinearMap.range_add_le f g)
    have himage := (LinearMap.range f).finrank_sup_add_finrank_inf_eq (LinearMap.range g)
    have hinf : finrank K (LinearMap.range f ⊓ LinearMap.range g : Submodule K V) = 0 := by
      omega
    have hd : Disjoint (LinearMap.range f) (LinearMap.range g) := by
      exact disjoint_iff.mpr (Submodule.finrank_eq_zero.mp hinf)
    refine ⟨hd, ?_⟩
    have heq := ker_add_of_disjoint f g hd
    rw [heq] at hfg
    apply Submodule.eq_top_of_finrank_eq
    omega
  · rintro ⟨hd, htop⟩
    rw [ker_add_of_disjoint f g hd] at hfg
    rw [htop, finrank_top] at hker
    omega

omit [FiniteDimensional K V] in
/-- The left image is contained in the total image for a rank-additive pair. -/
theorem range_left_le_range_add (f g : W →ₗ[K] V)
    (h : finrank K (LinearMap.range (f + g)) =
      finrank K (LinearMap.range f) + finrank K (LinearMap.range g)) :
    LinearMap.range f ≤ LinearMap.range (f + g) := by
  have hk := ((finrank_add_eq_iff f g).mp h).2
  intro v hv
  have hp : (v, (0 : V)) ∈ (LinearMap.range f).prod (LinearMap.range g) :=
    ⟨hv, Submodule.zero_mem _⟩
  rw [← LinearMap.range_prod_eq hk] at hp
  rcases hp with ⟨w, hw⟩
  have hwf : f w = v := congrArg Prod.fst hw
  have hwg : g w = 0 := congrArg Prod.snd hw
  refine ⟨w, ?_⟩
  change f w + g w = v
  rw [hwf, hwg, add_zero]

omit [FiniteDimensional K V] in
/-- The total kernel is contained in the left kernel for a rank-additive pair. -/
theorem ker_add_le_ker_left (f g : W →ₗ[K] V)
    (h : finrank K (LinearMap.range (f + g)) =
      finrank K (LinearMap.range f) + finrank K (LinearMap.range g)) :
    LinearMap.ker (f + g) ≤ LinearMap.ker f := by
  rw [ker_add_of_disjoint f g ((finrank_add_eq_iff f g).mp h).1]
  exact inf_le_left

def RankBelow (X Y : W →ₗ[K] V) : Prop :=
  finrank K (LinearMap.range Y) =
    finrank K (LinearMap.range X) + finrank K (LinearMap.range (Y - X))

omit [FiniteDimensional K W] [FiniteDimensional K V] in
theorem add_remainder (X Y : W →ₗ[K] V) : X + (Y - X) = Y := by
  rw [add_comm X, sub_add_cancel]

omit [FiniteDimensional K V] in
theorem rankBelow_iff (X Y : W →ₗ[K] V) :
    RankBelow X Y ↔
      Disjoint (LinearMap.range X) (LinearMap.range (Y - X)) ∧
        LinearMap.ker X ⊔ LinearMap.ker (Y - X) = ⊤ := by
  have h := finrank_add_eq_iff X (Y - X)
  rw [add_remainder] at h
  exact h

omit [FiniteDimensional K V] in
theorem range_le_of_rankBelow (X Y : W →ₗ[K] V) (h : RankBelow X Y) :
    LinearMap.range X ≤ LinearMap.range Y := by
  have h' : finrank K (LinearMap.range (X + (Y - X))) =
      finrank K (LinearMap.range X) + finrank K (LinearMap.range (Y - X)) := by
    rw [add_remainder]
    exact h
  simpa only [add_remainder] using range_left_le_range_add X (Y - X) h'

omit [FiniteDimensional K V] in
theorem ker_le_of_rankBelow (X Y : W →ₗ[K] V) (h : RankBelow X Y) :
    LinearMap.ker Y ≤ LinearMap.ker X := by
  have h' : finrank K (LinearMap.range (X + (Y - X))) =
      finrank K (LinearMap.range X) + finrank K (LinearMap.range (Y - X)) := by
    rw [add_remainder]
    exact h
  simpa only [add_remainder] using ker_add_le_ker_left X (Y - X) h'

omit [FiniteDimensional K V] in
theorem range_remainder_eq_range_on_kernel (X Y : W →ₗ[K] V) (h : RankBelow X Y) :
    LinearMap.range (Y - X) = LinearMap.range (Y.domRestrict (LinearMap.ker X)) := by
  have hc := ((rankBelow_iff X Y).mp h).2
  apply le_antisymm
  · rintro v ⟨w, hw⟩
    have ht : w ∈ LinearMap.ker X ⊔ LinearMap.ker (Y - X) := by rw [hc]; trivial
    rcases Submodule.mem_sup.mp ht with ⟨k, hk, j, hj, hkj⟩
    have hzk : (Y - X) k = (Y - X) w := by
      rw [← hkj, map_add, show (Y - X) j = 0 from hj, add_zero]
    refine ⟨⟨k, hk⟩, ?_⟩
    change Y k = v
    calc
      Y k = (Y - X) k := by
        change Y k = Y k - X k
        rw [show X k = 0 from hk, sub_zero]
      _ = (Y - X) w := hzk
      _ = v := hw
  · rintro v ⟨w, hw⟩
    refine ⟨(w : W), ?_⟩
    change Y w - X w = v
    rw [show X w = 0 from w.property, sub_zero]
    exact hw

omit [FiniteDimensional K V] in
theorem mem_ker_of_apply_mem_range_remainder (X Y : W →ₗ[K] V)
    (h : RankBelow X Y) (w : W) (hw : Y w ∈ LinearMap.range (Y - X)) :
    w ∈ LinearMap.ker X := by
  have hd := ((rankBelow_iff X Y).mp h).1
  have hz : (Y - X) w ∈ LinearMap.range (Y - X) := ⟨w, rfl⟩
  have hx : X w ∈ LinearMap.range (Y - X) := by
    have hs := (LinearMap.range (Y - X)).sub_mem hw hz
    have heq : Y w - (Y - X) w = X w := by
      simp only [LinearMap.sub_apply]
      abel
    exact heq ▸ hs
  exact Submodule.disjoint_def.mp hd (X w) ⟨w, rfl⟩ hx

end MaxCutGames.Appendix.RankAdditivity

namespace MaxCutGames.Appendix.CompressionCount

open Module
open MaxCutGames.Integration.BinaryLinear (F2)

universe u v w

variable (U : Type u) (K : Type v) (C : Type w)
variable [AddCommGroup U] [Module F2 U]
variable [AddCommGroup K] [Module F2 K]
variable [AddCommGroup C] [Module F2 C]

/-- Canonical rank-`dim U` map. -/
def base : (U × K) →ₗ[F2] (U × C) :=
  (LinearMap.inl F2 U C).comp (LinearMap.fst F2 U K)

@[simp] theorem base_apply (p : U × K) : base U K C p = (p.1, 0) := rfl

variable {U K C}

/-- Compress by restricting to the second domain factor and taking the second
codomain coordinate. -/
def compress (Y : (U × K) →ₗ[F2] (U × C)) : K →ₗ[F2] C :=
  (LinearMap.snd F2 U C).comp (Y.comp (LinearMap.inr F2 U K))

@[simp] theorem compress_apply (Y : (U × K) →ₗ[F2] (U × C)) (k : K) :
    compress Y k = (Y (0, k)).2 := rfl

/-- The actual rank-order compression fiber; subtraction agrees with addition
over the binary field. -/
def Fiber (Z : K →ₗ[F2] C) :=
  {Y : (U × K) →ₗ[F2] (U × C) //
    finrank F2 Y.range = finrank F2 U + finrank F2 (Y - base U K C).range ∧
      compress Y = Z}

abbrev Parameters (Z : K →ₗ[F2] C) :=
  (Z.range →ₗ[F2] U) × (U →ₗ[F2] Z.range)

def graph (Z : K →ₗ[F2] C) (F : Z.range →ₗ[F2] U) :
    Z.range →ₗ[F2] (U × C) := F.prod Z.range.subtype

def inclusion (Z : K →ₗ[F2] C) : (U × Z.range) →ₗ[F2] (U × C) :=
  (LinearMap.id : U →ₗ[F2] U).prodMap Z.range.subtype

def lower (Z : K →ₗ[F2] C) (H : U →ₗ[F2] Z.range) :
    (U × K) →ₗ[F2] Z.range := H.coprod Z.rangeRestrict

/-- The block matrix `[I+FH,FZ;H,Z]`. -/
def lift (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z) :
    (U × K) →ₗ[F2] (U × C) :=
  base U K C + (graph Z P.1).comp (lower Z P.2)

@[simp] theorem lift_apply (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z)
    (p : U × K) :
    lift Z P p = (p.1 + P.1 (P.2 p.1 + Z.rangeRestrict p.2),
      ((P.2 p.1 : Z.range) : C) + Z p.2) := by
  simp [lift, graph, lower]

@[simp] theorem compress_lift (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z) :
    compress (lift Z P) = Z := by
  ext k
  simp

theorem graph_injective (Z : K →ₗ[F2] C) (F : Z.range →ₗ[F2] U) :
    Function.Injective (graph Z F) := by
  intro a b h
  exact Subtype.ext (congrArg Prod.snd h)

theorem inclusion_injective (Z : K →ₗ[F2] C) :
    Function.Injective (inclusion (U := U) Z) := by
  intro a b h
  exact Prod.ext (by simpa [inclusion] using congrArg Prod.fst h)
    (Subtype.ext (by simpa [inclusion] using congrArg Prod.snd h))

theorem lower_surjective (Z : K →ₗ[F2] C) (H : U →ₗ[F2] Z.range) :
    Function.Surjective (lower Z H) := by
  intro c
  obtain ⟨k, hk⟩ := Z.surjective_rangeRestrict c
  refine ⟨(0, k), ?_⟩
  simpa [lower] using hk

theorem range_lift_sub_base (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z) :
    (lift Z P - base U K C).range = (graph Z P.1).range := by
  rw [lift, add_sub_cancel_left]
  exact LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (lower_surjective Z P.2))

theorem range_lift (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z) :
    (lift Z P).range = (inclusion (U := U) Z).range := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    refine ⟨(p.1 + P.1 (P.2 p.1 + Z.rangeRestrict p.2),
      P.2 p.1 + Z.rangeRestrict p.2), ?_⟩
    simp [inclusion]
  · rintro _ ⟨⟨u, c⟩, rfl⟩
    obtain ⟨k, hk⟩ := Z.surjective_rangeRestrict (c - P.2 (u - P.1 c))
    refine ⟨(u - P.1 c, k), ?_⟩
    have hc : P.2 (u - P.1 c) + Z.rangeRestrict k = c := by rw [hk]; abel
    apply Prod.ext
    · change u - P.1 c + P.1 (P.2 (u - P.1 c) + Z.rangeRestrict k) = u
      rw [hc]
      abel
    · simpa [inclusion] using congrArg Subtype.val hc

variable [FiniteDimensional F2 U] [FiniteDimensional F2 K] [FiniteDimensional F2 C]

omit [FiniteDimensional F2 U] [FiniteDimensional F2 K] [FiniteDimensional F2 C] in
theorem finrank_base : finrank F2 (base U K C).range = finrank F2 U := by
  rw [base, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr LinearMap.fst_surjective)]
  exact LinearMap.finrank_range_of_inj LinearMap.inl_injective

omit [FiniteDimensional F2 C] in
theorem lift_rank_order (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z) :
    finrank F2 (lift Z P).range =
      finrank F2 U + finrank F2 (lift Z P - base U K C).range := by
  rw [range_lift, range_lift_sub_base,
    LinearMap.finrank_range_of_inj (inclusion_injective (U := U) Z),
    LinearMap.finrank_range_of_inj (graph_injective Z P.1), Module.finrank_prod]

def toFiber (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z) : Fiber (U := U) Z :=
  ⟨lift Z P, lift_rank_order Z P, compress_lift Z P⟩

omit [FiniteDimensional F2 U] [FiniteDimensional F2 K] [FiniteDimensional F2 C] in
theorem lift_injective (Z : K →ₗ[F2] C) :
    Function.Injective (lift (U := U) Z) := by
  rintro ⟨F, H⟩ ⟨G, J⟩ h
  have hH : H = J := by
    ext u
    have he := congrArg (fun f => (f (u, 0)).2) h
    simpa using he
  have hF : F = G := by
    ext c
    obtain ⟨k, hk⟩ := Z.surjective_rangeRestrict c
    have he := congrArg (fun f => (f (0, k)).1) h
    simpa [hk] using he
  exact Prod.ext hF hH

theorem natCard_linearMap : Nat.card (U →ₗ[F2] C) =
    2 ^ (finrank F2 U * finrank F2 C) := by
  let e : (Fin (finrank F2 U) → C) ≃ (U →ₗ[F2] C) :=
    ((Module.finBasis F2 U).constr F2).toEquiv
  calc
    Nat.card (U →ₗ[F2] C) = Nat.card C ^ finrank F2 U := by
      rw [← Nat.card_congr e, Nat.card_fun, Nat.card_fin]
    _ = (2 ^ finrank F2 C) ^ finrank F2 U := by
      rw [Module.natCard_eq_pow_finrank (K := F2) (V := C)]
      simp [F2, Nat.card_eq_fintype_card]
    _ = 2 ^ (finrank F2 U * finrank F2 C) := by
      rw [← pow_mul, Nat.mul_comm]

omit [FiniteDimensional F2 C] in
theorem card_parameters (Z : K →ₗ[F2] C) : Nat.card (Parameters (U := U) Z) =
    2 ^ (2 * finrank F2 U * finrank F2 Z.range) := by
  rw [Nat.card_prod, natCard_linearMap, natCard_linearMap, ← pow_add]
  congr 1
  ring

omit [FiniteDimensional F2 C] in
/-- Rank additivity supplies exactly the image/kernel hypotheses used by the
block argument. -/
theorem fiber_geometry (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    Disjoint (base U K C).range (Y.val - base U K C).range ∧
      (base U K C).ker ⊔ (Y.val - base U K C).ker = ⊤ := by
  apply (RankAdditivity.finrank_add_eq_iff (base U K C) (Y.val - base U K C)).mp
  have heq : base U K C + (Y.val - base U K C) = Y.val := by abel
  rw [heq, finrank_base]
  exact Y.property.1

omit [FiniteDimensional F2 C] in
/-- Every lower coordinate of a map in the fiber lies in the compressed image.
This is the step that permits taking `H : U → range Z`. -/
theorem snd_mem_range (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) (p : U × K) :
    (Y.val p).2 ∈ Z.range := by
  have hp : p ∈ (base U K C).ker ⊔ (Y.val - base U K C).ker := by
    rw [(fiber_geometry Z Y).2]
    trivial
  rcases Submodule.mem_sup.mp hp with ⟨a, ha, b, hb, hab⟩
  have ha0 : a.1 = 0 := congrArg Prod.fst ha
  have haeq : a = (0, a.2) := Prod.ext ha0 rfl
  have hDb : Y.val b = base U K C b := sub_eq_zero.mp hb
  refine ⟨a.2, ?_⟩
  have hcomp := LinearMap.congr_fun Y.property.2 a.2
  calc
    Z a.2 = (Y.val (0, a.2)).2 := hcomp.symm
    _ = (Y.val a).2 := congrArg (fun q => (Y.val q).2) haeq.symm
    _ = (Y.val (a + b)).2 := by simp [map_add, hDb]
    _ = (Y.val p).2 := congrArg (fun q => (Y.val q).2) hab

/-- Choose a linear section of the map onto its image. -/
noncomputable def linearSection (Z : K →ₗ[F2] C) : Z.range →ₗ[F2] K :=
  Classical.choose
    (Z.rangeRestrict.exists_rightInverse_of_surjective Z.range_rangeRestrict)

omit [FiniteDimensional F2 C] in
theorem section_spec (Z : K →ₗ[F2] C) (c : Z.range) :
    Z.rangeRestrict (linearSection Z c) = c :=
  LinearMap.congr_fun (Classical.choose_spec
    (Z.rangeRestrict.exists_rightInverse_of_surjective Z.range_rangeRestrict)) c

noncomputable def extractedF (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    Z.range →ₗ[F2] U :=
  (LinearMap.fst F2 U C).comp
    (Y.val.comp ((LinearMap.inr F2 U K).comp (linearSection Z)))

def extractedH (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    U →ₗ[F2] Z.range :=
  ((LinearMap.snd F2 U C).comp (Y.val.comp (LinearMap.inl F2 U K))).codRestrict
    Z.range (fun u => snd_mem_range Z Y (u, 0))

omit [FiniteDimensional F2 C] in
theorem extracted_lower (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) (p : U × K) :
    extractedH Z Y p.1 + Z.rangeRestrict p.2 =
      ⟨(Y.val p).2, snd_mem_range Z Y p⟩ := by
  apply Subtype.ext
  change (Y.val (p.1, 0)).2 + Z p.2 = (Y.val p).2
  rw [← LinearMap.congr_fun Y.property.2 p.2]
  change (Y.val (p.1, 0)).2 + (Y.val (0, p.2)).2 = (Y.val p).2
  rw [← Prod.snd_add, ← map_add]
  simp

omit [FiniteDimensional F2 C] in
/-- On the difference image, the lower coordinate uniquely determines the
upper coordinate. -/
theorem difference_ext_snd (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z)
    (p q : U × K) (h : (Y.val p).2 = (Y.val q).2) :
    (Y.val - base U K C) p = (Y.val - base U K C) q := by
  let D := Y.val - base U K C
  have hbottom : (D (p - q)).2 = 0 := by
    change ((Y.val - base U K C) (p - q)).2 = 0
    simp only [LinearMap.sub_apply, map_sub, Prod.snd_sub, base_apply]
    simpa using sub_eq_zero.mpr h
  have hzero : D (p - q) = 0 := by
    apply Submodule.disjoint_def.mp (fiber_geometry Z Y).1 (D (p - q))
    · refine ⟨((D (p - q)).1, 0), ?_⟩
      exact Prod.ext rfl hbottom.symm
    · exact ⟨p - q, rfl⟩
  exact sub_eq_zero.mp (by simpa only [map_sub] using hzero)

omit [FiniteDimensional F2 C] in
theorem lift_extracted (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    lift Z (extractedF Z Y, extractedH Z Y) = Y.val := by
  apply LinearMap.ext
  intro p
  let c : Z.range := ⟨(Y.val p).2, snd_mem_range Z Y p⟩
  have hq : (Y.val (0, linearSection Z c)).2 = (Y.val p).2 := by
    calc
      (Y.val (0, linearSection Z c)).2 = Z (linearSection Z c) :=
        LinearMap.congr_fun Y.property.2 (linearSection Z c)
      _ = (c : C) := congrArg Subtype.val (section_spec Z c)
      _ = (Y.val p).2 := rfl
  have hd := congrArg Prod.fst (difference_ext_snd Z Y p (0, linearSection Z c) hq.symm)
  change (Y.val p).1 - p.1 = (Y.val (0, linearSection Z c)).1 - 0 at hd
  apply Prod.ext
  · change p.1 + extractedF Z Y
      (extractedH Z Y p.1 + Z.rangeRestrict p.2) = (Y.val p).1
    rw [extracted_lower]
    change p.1 + (Y.val (0, linearSection Z c)).1 = (Y.val p).1
    rw [sub_zero] at hd
    rw [← hd]
    abel
  · simpa using congrArg Subtype.val (extracted_lower Z Y p)

omit [FiniteDimensional F2 C] in
theorem toFiber_bijective (Z : K →ₗ[F2] C) :
    Function.Bijective (toFiber (U := U) Z) := by
  constructor
  · intro P Q h
    exact lift_injective Z (congrArg Subtype.val h)
  · intro Y
    exact ⟨(extractedF Z Y, extractedH Z Y), Subtype.ext (lift_extracted Z Y)⟩

/-- The exact compression fiber is in bijection with two independent spaces of
linear maps. No rank or cardinality claim is an assumption of this equivalence. -/
noncomputable def fiberEquiv (Z : K →ₗ[F2] C) :
    Parameters (U := U) Z ≃ Fiber (U := U) Z :=
  Equiv.ofBijective (toFiber Z) (toFiber_bijective Z)

omit [FiniteDimensional F2 C] in
theorem fiber_remainder_rank (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    finrank F2 (Y.val - base U K C).range = finrank F2 Z.range := by
  obtain ⟨P, hP⟩ := (toFiber_bijective Z).2 Y
  have hY : lift Z P = Y.val := congrArg Subtype.val hP
  rw [← hY, range_lift_sub_base]
  exact LinearMap.finrank_range_of_inj (graph_injective Z P.1)

omit [FiniteDimensional F2 C] in
theorem fiber_rank (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    finrank F2 Y.val.range = finrank F2 U + finrank F2 Z.range := by
  rw [Y.property.1, fiber_remainder_rank]

omit [FiniteDimensional F2 C] in
/-- Lemma A.2 in arbitrary finite-dimensional block coordinates. -/
theorem card_fiber (Z : K →ₗ[F2] C) : Nat.card (Fiber (U := U) Z) =
    2 ^ (2 * finrank F2 U * finrank F2 Z.range) := by
  rw [← Nat.card_congr (fiberEquiv (U := U) Z)]
  exact card_parameters Z

end MaxCutGames.Appendix.CompressionCount

/-! Actual subspace cardinality bounds used in (5.12)--(5.13).

Every subspace is the image of a projection endomorphism. Thus the set of all
subspaces is a quotient of the endomorphism space. The exact finite-field
linear-map count is reused from `Appendix.CompressionCount`.
-/

namespace MaxCutGames.Fourier.MatrixSubspaceCount

open Module
open MaxCutGames.Integration.BinaryLinear (F2)

section GeneralField

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Taking the image of an endomorphism reaches every actual subspace. -/
theorem endomorphism_range_surjective :
    Function.Surjective (fun f : V →ₗ[K] V => LinearMap.range f) := by
  intro S
  obtain ⟨T, hT⟩ := S.exists_isCompl
  exact ⟨S.projection T hT, Submodule.range_projection hT⟩

theorem card_subspaces_le_endomorphisms [Finite V] :
    Nat.card (Submodule K V) ≤ Nat.card (V →ₗ[K] V) := by
  let : Finite (V →ₗ[K] V) := Finite.of_injective
    (fun f : V →ₗ[K] V => (f : V → V)) DFunLike.coe_injective
  exact Nat.card_le_card_of_surjective _ endomorphism_range_surjective

end GeneralField

variable {C : Type*} [AddCommGroup C] [Module F2 C] [Module.Finite F2 C]

private theorem finite_color_space_inline_MatrixSubspaceCount : Finite C :=
  Finite.of_injective (Module.finBasis F2 C).equivFun
    (Module.finBasis F2 C).equivFun.injective

private theorem finite_endomorphisms_inline_MatrixSubspaceCount : Finite (C →ₗ[F2] C) := by
  let : Finite C := finite_color_space_inline_MatrixSubspaceCount
  exact Finite.of_injective (fun f : C →ₗ[F2] C => (f : C → C)) DFunLike.coe_injective

private theorem finite_subspaces_inline_MatrixSubspaceCount : Finite (Submodule F2 C) := by
  let : Finite (C →ₗ[F2] C) := finite_endomorphisms_inline_MatrixSubspaceCount
  exact Finite.of_surjective _ endomorphism_range_surjective

theorem card_binary_subspaces_le :
    Nat.card (Submodule F2 C) ≤ 2 ^ (finrank F2 C * finrank F2 C) := by
  let : Finite C := finite_color_space_inline_MatrixSubspaceCount
  calc
    _ ≤ Nat.card (C →ₗ[F2] C) := card_subspaces_le_endomorphisms
    _ = _ := MaxCutGames.Appendix.CompressionCount.natCard_linearMap

theorem card_binary_subspaces_le_of_finrank_le (s : ℕ) (hs : finrank F2 C ≤ s) :
    Nat.card (Submodule F2 C) ≤ 2 ^ (s * s) := by
  exact card_binary_subspaces_le.trans
    (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul hs hs))

theorem card_admissible_subspaces_le (P : Submodule F2 C → Prop) :
    Nat.card {S : Submodule F2 C // P S} ≤ 2 ^ (finrank F2 C * finrank F2 C) := by
  let : Finite (Submodule F2 C) := finite_subspaces_inline_MatrixSubspaceCount
  exact (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
    card_binary_subspaces_le

/-- Counting fixed colors together with actual admissible subspaces gives
precisely the `q * 2^(s*s)` denominator budget from (5.13). -/
theorem card_color_admissible_subspaces_le (P : Submodule F2 C → Prop) :
    Nat.card (C × {S : Submodule F2 C // P S}) ≤
      Nat.card C * 2 ^ (finrank F2 C * finrank F2 C) := by
  rw [Nat.card_prod]
  exact Nat.mul_le_mul_left _ (card_admissible_subspaces_le P)

theorem card_color_admissible_subspaces_le_of_finrank_le
    (P : Submodule F2 C → Prop) (s : ℕ) (hs : finrank F2 C ≤ s) :
    Nat.card (C × {S : Submodule F2 C // P S}) ≤ Nat.card C * 2 ^ (s * s) := by
  exact (card_color_admissible_subspaces_le P).trans
    (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul hs hs)))

end MaxCutGames.Fourier.MatrixSubspaceCount

namespace MaxCutGames.Fourier.MatrixEnergy

open scoped BigOperators

variable {Q : Type*} {I : Q → Type*} [Fintype Q] [∀ q, Fintype (I q)]

/-- Squared coefficient energy, averaged using the supplied question weights. -/
noncomputable def energy (weight : Q → ℝ) (a : (q : Q) → I q → ℝ) : ℝ :=
  ∑ q, weight q * ∑ i, a q i ^ 2

/-- Squared energy retained by a coordinate projection. -/
noncomputable def cutoffEnergy (weight : Q → ℝ) (keep : (q : Q) → I q → Prop)
    (a : (q : Q) → I q → ℝ) : ℝ := by
  classical
  exact ∑ q, weight q * ∑ i, if keep q i then a q i ^ 2 else 0

/-- Diagonal spectral quadratic form. -/
noncomputable def spectralEnergy (weight : Q → ℝ) (eigen a : (q : Q) → I q → ℝ) : ℝ :=
  ∑ q, weight q * ∑ i, eigen q i * a q i ^ 2

theorem energy_nonneg (weight : Q → ℝ) (a : (q : Q) → I q → ℝ)
    (hw : ∀ q, 0 ≤ weight q) : 0 ≤ energy weight a := by
  exact Finset.sum_nonneg (fun q _ => mul_nonneg (hw q)
    (Finset.sum_nonneg (fun i _ => sq_nonneg (a q i))))

theorem cutoffEnergy_nonneg (weight : Q → ℝ) (keep : (q : Q) → I q → Prop)
    (a : (q : Q) → I q → ℝ) (hw : ∀ q, 0 ≤ weight q) :
    0 ≤ cutoffEnergy weight keep a := by
  classical
  unfold cutoffEnergy
  apply Finset.sum_nonneg
  intro q _
  apply mul_nonneg (hw q)
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact sq_nonneg _
  · exact le_rfl

/-- The projection onto any set of coefficient indices is a contraction in
the weighted squared norm. -/
theorem cutoffEnergy_le_energy (weight : Q → ℝ) (keep : (q : Q) → I q → Prop)
    (a : (q : Q) → I q → ℝ) (hw : ∀ q, 0 ≤ weight q) :
    cutoffEnergy weight keep a ≤ energy weight a := by
  classical
  apply Finset.sum_le_sum
  intro q _
  apply mul_le_mul_of_nonneg_left _ (hw q)
  apply Finset.sum_le_sum
  intro i _
  split_ifs <;> nlinarith [sq_nonneg (a q i)]

/-- Retained and discarded coefficient coordinates are orthogonal: their
energies add exactly to the original energy. -/
theorem energy_split (weight : Q → ℝ) (keep : (q : Q) → I q → Prop) (a : (q : Q) → I q → ℝ) :
    energy weight a = cutoffEnergy weight keep a +
      cutoffEnergy weight (fun q i => ¬ keep q i) a := by
  classical
  unfold energy cutoffEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : keep q i <;> simp [h]

/-- A spectral multiplier bounded by one on retained indices and by `η`
elsewhere contributes at most retained energy plus `η` times total energy. -/
theorem spectralEnergy_le_cutoff_add
    (weight : Q → ℝ) (keep : (q : Q) → I q → Prop) (eigen a : (q : Q) → I q → ℝ) (η : ℝ)
    (hw : ∀ q, 0 ≤ weight q) (hη : 0 ≤ η)
    (hone : ∀ q i, eigen q i ≤ 1)
    (hhigh : ∀ q i, ¬ keep q i → eigen q i ≤ η) :
    spectralEnergy weight eigen a ≤ cutoffEnergy weight keep a + η * energy weight a := by
  classical
  have hpoint (q : Q) (i : I q) :
      eigen q i * a q i ^ 2 ≤ (if keep q i then a q i ^ 2 else 0) + η * a q i ^ 2 := by
    by_cases hk : keep q i
    · have h := mul_le_mul_of_nonneg_right (hone q i) (sq_nonneg (a q i))
      have hn := mul_nonneg hη (sq_nonneg (a q i))
      simp only [hk, ite_true]
      nlinarith
    · simpa only [hk, ite_false, zero_add] using
        mul_le_mul_of_nonneg_right (hhigh q i hk) (sq_nonneg (a q i))
  calc
    spectralEnergy weight eigen a
        ≤ ∑ q, weight q * ∑ i,
          ((if keep q i then a q i ^ 2 else 0) + η * a q i ^ 2) := by
      apply Finset.sum_le_sum
      intro q _
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hpoint q i)) (hw q)
    _ = cutoffEnergy weight keep a + η * energy weight a := by
      simp only [cutoffEnergy, energy, Finset.sum_add_distrib, ← Finset.mul_sum, mul_add]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring

/-- Unit total energy and spectral value above `δ` force retained energy above
`δ/2` when all discarded multipliers are at most `δ/2`. -/
theorem cutoffEnergy_gt_half
    (weight : Q → ℝ) (keep : (q : Q) → I q → Prop) (eigen a : (q : Q) → I q → ℝ) (δ : ℝ)
    (hw : ∀ q, 0 ≤ weight q) (hδ : 0 ≤ δ)
    (hone : ∀ q i, eigen q i ≤ 1)
    (hhigh : ∀ q i, ¬ keep q i → eigen q i ≤ δ / 2)
    (htotal : energy weight a = 1) (hvalue : δ < spectralEnergy weight eigen a) :
    δ / 2 < cutoffEnergy weight keep a := by
  have h := spectralEnergy_le_cutoff_add weight keep eigen a (δ / 2)
    hw (by linarith) hone hhigh
  rw [htotal] at h
  linarith

/-- The elementary square bound, summed over the retained coefficients.  The
discarded term on the right uses the full coefficient difference, giving the
contraction needed for equation (5.11) without introducing square roots. -/
theorem cutoffEnergy_le_twice_difference_add
    (weight : Q → ℝ) (keep : (q : Q) → I q → Prop) (H G : (q : Q) → I q → ℝ)
    (hw : ∀ q, 0 ≤ weight q) :
    cutoffEnergy weight keep H ≤
      2 * energy weight (fun q i => H q i - G q i) + 2 * cutoffEnergy weight keep G := by
  classical
  have hpoint (q : Q) (i : I q) :
      (if keep q i then H q i ^ 2 else 0) ≤
        2 * (H q i - G q i) ^ 2 + 2 * (if keep q i then G q i ^ 2 else 0) := by
    by_cases hk : keep q i
    · simp only [hk, ite_true]
      nlinarith [sq_nonneg (H q i - 2 * G q i)]
    · simp only [hk, ite_false, mul_zero, add_zero]
      nlinarith [sq_nonneg (H q i - G q i)]
  calc
    cutoffEnergy weight keep H ≤
        ∑ q, weight q * ∑ i,
          (2 * (H q i - G q i) ^ 2 + 2 * (if keep q i then G q i ^ 2 else 0)) := by
      apply Finset.sum_le_sum
      intro q _
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hpoint q i)) (hw q)
    _ = 2 * energy weight (fun q i => H q i - G q i) +
        2 * cutoffEnergy weight keep G := by
      simp only [energy, cutoffEnergy, Finset.sum_add_distrib, ← Finset.mul_sum, mul_add]
      congr 1 <;> rw [Finset.mul_sum] <;>
        apply Finset.sum_congr rfl <;> intro q _ <;> ring

theorem deleted_energy_gt_eighth
    (weight : Q → ℝ) (keep : (q : Q) → I q → Prop) (H G : (q : Q) → I q → ℝ) (δ : ℝ)
    (hw : ∀ q, 0 ≤ weight q)
    (hlarge : δ / 2 < cutoffEnergy weight keep H)
    (hsmall : cutoffEnergy weight keep G ≤ δ / 8) :
    δ / 8 < energy weight (fun q i => H q i - G q i) := by
  have h := cutoffEnergy_le_twice_difference_add weight keep H G hw
  linarith

/-- Squared Boolean functions equal their values under a finite weighted sum. -/
theorem boolean_energy_eq_mass (weight : Q → ℝ) (H : (q : Q) → I q → ℝ)
    (hbool : ∀ q i, H q i = 0 ∨ H q i = 1) :
    energy weight H = ∑ q, weight q * ∑ i, H q i := by
  unfold energy
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rcases hbool q i with h | h <;> simp [h]

/-- A finite union bound for fractional removed mass dominated by indicator
events. Both the event choice and the removed value may depend on the outcome. -/
theorem weighted_union_bound {Ω J : Type*} [Fintype Ω] [Fintype J]
    (weight value : Ω → ℝ) (event : J → Ω → Prop)
    [∀ j, DecidablePred (event j)]
    (hw : ∀ ω, 0 ≤ weight ω) (hvalue : ∀ ω, value ω ≤ 1)
    (hcover : ∀ ω, 0 < value ω → ∃ j, event j ω) :
    (∑ ω, weight ω * value ω) ≤
      ∑ j, ∑ ω, weight ω * (if event j ω then (1 : ℝ) else 0) := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (hw ω)
  by_cases hp : 0 < value ω
  · obtain ⟨j, hj⟩ := hcover ω hp
    have hs : (if event j ω then (1 : ℝ) else 0) ≤
        ∑ k, if event k ω then (1 : ℝ) else 0 := by
      apply Finset.single_le_sum (s := Finset.univ)
        (f := fun k : J => if event k ω then (1 : ℝ) else 0) (a := j)
      · intro k _; split_ifs <;> norm_num
      · exact Finset.mem_univ j
    exact le_trans (hvalue ω) (by simpa [hj] using hs)
  · exact le_trans (le_of_not_gt hp) (Finset.sum_nonneg (by intro j _; split_ifs <;> norm_num))

/-- Finite real pigeonhole principle for the one fixed color/subspace choice. -/
theorem exists_fixed_event {J : Type*} [Fintype J] (mass : J → ℝ)
    (threshold budget : ℝ)
    (hcount : (Fintype.card J : ℝ) * threshold ≤ budget)
    (hmass : budget < ∑ j, mass j) : ∃ j, threshold < mass j := by
  classical
  by_contra h
  push Not at h
  have hs : (∑ j, mass j) ≤ (Fintype.card J : ℝ) * threshold := by
    calc
      (∑ j, mass j) ≤ ∑ _j : J, threshold := Finset.sum_le_sum (fun j _ => h j)
      _ = _ := by simp
  linarith

/-- The explicit denominator in (5.13), for any supplied event-count bound. -/
theorem exists_fixed_event_scaled {J : Type*} [Fintype J]
    (mass : J → ℝ) (N : ℕ) (δ : ℝ)
    (hN : 0 < N) (hδ : 0 ≤ δ) (hcard : Fintype.card J ≤ N)
    (hmass : δ / 8 < ∑ j, mass j) :
    ∃ j, δ / (8 * (N : ℝ)) < mass j := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hcardreal : (Fintype.card J : ℝ) ≤ N := by exact_mod_cast hcard
  have hthreshold : 0 ≤ δ / (8 * (N : ℝ)) :=
    div_nonneg hδ (mul_nonneg (by norm_num) hNreal.le)
  have hcancel : (N : ℝ) * (δ / (8 * (N : ℝ))) = δ / 8 := by
    field_simp [ne_of_gt hNreal]
  apply exists_fixed_event mass (δ / (8 * (N : ℝ))) (δ / 8) _ hmass
  rw [← hcancel]
  exact mul_le_mul_of_nonneg_right hcardreal hthreshold

section LinearMaps

open MatrixCharacters MatrixFourier

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- The actual rank of a Fourier index restricted to the alphabet subspace. -/
noncomputable def linearRankOn (C : Submodule F2 F) (S : F →ₗ[F2] E) : ℕ :=
  Module.finrank F2 (LinearMap.range (S.comp C.subtype))

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem linearRankOn_top (S : F →ₗ[F2] E) :
    linearRankOn (⊤ : Submodule F2 F) S =
      Module.finrank F2 (LinearMap.range S) := by
  have hrange : LinearMap.range (S.comp (⊤ : Submodule F2 F).subtype) =
      LinearMap.range S := by
    ext x
    constructor
    · rintro ⟨v, hv⟩
      exact ⟨v.1, hv⟩
    · rintro ⟨v, hv⟩
      exact ⟨⟨v, by simp⟩, hv⟩
  exact congrArg (fun P : Submodule F2 E => Module.finrank F2 P) hrange

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
/-- Restricting to the image of a symbol embedding has the same image rank
as composition with that embedding, even when it is not injective. -/
theorem linearRankOn_range {V : Type*} [AddCommGroup V] [Module F2 V]
    (S : F →ₗ[F2] E) (ι : V →ₗ[F2] F) :
    linearRankOn (LinearMap.range ι) S =
      Module.finrank F2 (LinearMap.range (S.comp ι)) := by
  have hrange : LinearMap.range (S.comp (LinearMap.range ι).subtype) =
      LinearMap.range (S.comp ι) := by
    ext x
    constructor
    · rintro ⟨v, hv⟩
      obtain ⟨u, hu⟩ := v.property
      refine ⟨u, ?_⟩
      change S (ι u) = x
      rw [hu]
      exact hv
    · rintro ⟨u, hu⟩
      exact ⟨⟨ι u, ⟨u, rfl⟩⟩, hu⟩
  exact congrArg (fun P : Submodule F2 E => Module.finrank F2 P) hrange

/-- Projection onto trace characters whose index has bounded rank on `C`. -/
noncomputable def rankProjection (C : Submodule F2 F) (r : ℕ)
    (f : (E →ₗ[F2] F) → ℝ) : (E →ₗ[F2] F) → ℝ := by
  classical
  exact ∑ S : F →ₗ[F2] E,
    (if linearRankOn C S ≤ r then linearCoeff f S else 0) •
      (fun X => (linearTraceCharacter S X).re)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_sub (f g : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (fun X => f X - g X) S = linearCoeff f S - linearCoeff g S := by
  simp only [linearCoeff, sub_mul, Finset.expect_sub_distrib]

/-- The genuine function-space projection acts by the claimed coefficient mask. -/
theorem linearCoeff_rankProjection (C : Submodule F2 F) (r : ℕ)
    (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (rankProjection C r f) S =
      if linearRankOn C S ≤ r then linearCoeff f S else 0 := by
  classical
  unfold rankProjection
  rw [linearCoeff_sum]
  simp only [linearCoeff_smul, linearCoeff_character, mul_ite, mul_one, mul_zero]
  simp

/-- Squared norm of the actual projection equals the retained coefficient mass. -/
theorem rankProjection_parseval (C : Submodule F2 F) (r : ℕ)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, rankProjection C r f X ^ 2) =
      ∑ S : F →ₗ[F2] E, if linearRankOn C S ≤ r then linearCoeff f S ^ 2 else 0 := by
  classical
  rw [← linear_parseval]
  apply Finset.sum_congr rfl
  intro S _
  rw [linearCoeff_rankProjection]
  split_ifs <;> simp

/-- Contraction for the actual rank projection with the uniform function norm. -/
theorem rankProjection_contraction (C : Submodule F2 F) (r : ℕ)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, rankProjection C r f X ^ 2) ≤ 𝔼 X, f X ^ 2 := by
  classical
  rw [rankProjection_parseval, ← linear_parseval]
  apply Finset.sum_le_sum
  intro S _
  split_ifs
  · exact le_rfl
  · exact sq_nonneg _

/-- The projected part is orthogonal to the discarded part in the actual
uniform function inner product. -/
theorem rankProjection_orthogonal (C : Submodule F2 F) (r : ℕ)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, rankProjection C r f X * (f X - rankProjection C r f X)) = 0 := by
  classical
  rw [← linear_parseval_inner]
  apply Finset.sum_eq_zero
  intro S _
  rw [linearCoeff_sub, linearCoeff_rankProjection]
  split_ifs <;> simp

theorem linear_energy_parseval (weight : Q → ℝ) (f : Q → (E →ₗ[F2] F) → ℝ) :
    energy weight (fun q S => linearCoeff (f q) S) =
      ∑ q, weight q * (𝔼 X, f q X ^ 2) := by
  simp only [energy, linear_parseval]

theorem linear_difference_energy_parseval (weight : Q → ℝ)
    (H G : Q → (E →ₗ[F2] F) → ℝ) :
    energy weight (fun q S => linearCoeff (H q) S - linearCoeff (G q) S) =
      ∑ q, weight q * (𝔼 X, (H q X - G q X) ^ 2) := by
  simp only [← linearCoeff_sub, linear_energy_parseval]

/-- Equation (5.11) now for actual functions on a binary linear-map space,
using the actual restriction rank and trace Fourier coefficients. -/
theorem linear_deleted_energy_gt_eighth
    (weight : Q → ℝ) (C : Submodule F2 F) (r : ℕ)
    (H G : Q → (E →ₗ[F2] F) → ℝ) (δ : ℝ)
    (hw : ∀ q, 0 ≤ weight q)
    (hlarge : δ / 2 < cutoffEnergy weight (fun _ S => linearRankOn C S ≤ r)
      (fun q S => linearCoeff (H q) S))
    (hsmall : cutoffEnergy weight (fun _ S => linearRankOn C S ≤ r)
      (fun q S => linearCoeff (G q) S) ≤ δ / 8) :
    δ / 8 < ∑ q, weight q * (𝔼 X, (H q X - G q X) ^ 2) := by
  rw [← linear_difference_energy_parseval]
  exact deleted_energy_gt_eighth weight (fun _ S => linearRankOn C S ≤ r)
    (fun q S => linearCoeff (H q) S) (fun q S => linearCoeff (G q) S)
    δ hw hlarge hsmall

/-- Color indicator of one actual labeling. -/
noncomputable def colorIndicator {X Y : Type*} (label : X → Y) (y : Y) : X → ℝ := by
  classical
  exact fun x => if label x = y then 1 else 0

theorem colorIndicator_partition {X Y : Type*} [Fintype Y]
    (label : X → Y) (x : X) : ∑ y, colorIndicator label y x ^ 2 = 1 := by
  classical
  simp [colorIndicator, eq_comm]

/-- Parseval for all color indicators sums to exactly one, with the correct
uniform primal normalization and counting measure on Fourier indices. -/
theorem colorIndicator_parseval {Y : Type*} [Fintype Y]
    (label : (E →ₗ[F2] F) → Y) :
    (∑ y, ∑ S : F →ₗ[F2] E, linearCoeff (colorIndicator label y) S ^ 2) = 1 := by
  simp_rw [linear_parseval]
  rw [← Finset.expect_sum_comm]
  simp_rw [colorIndicator_partition]
  exact Fintype.expect_const 1

/-- Fourier coefficient array for a family of labelings, including color as
part of the component index. -/
noncomputable def labelingCoeff {Y : Type*}
    (label : Q → (E →ₗ[F2] F) → Y) (qy : Q × Y) (S : F →ₗ[F2] E) : ℝ :=
  linearCoeff (colorIndicator (label qy.1) qy.2) S

theorem labelingCoeff_energy_one {Y : Type*} [Fintype Y]
    (weight : Q → ℝ) (label : Q → (E →ₗ[F2] F) → Y)
    (hnorm : ∑ q, weight q = 1) :
    energy (fun qy : Q × Y => weight qy.1) (labelingCoeff label) = 1 := by
  classical
  calc
    energy (fun qy : Q × Y => weight qy.1) (labelingCoeff label) =
        ∑ q, weight q * (∑ y, ∑ S : F →ₗ[F2] E,
          linearCoeff (colorIndicator (label q) y) S ^ 2) := by
      simp only [energy, labelingCoeff, Fintype.sum_prod_type, Finset.mul_sum]
    _ = ∑ q, weight q := by simp only [colorIndicator_parseval, mul_one]
    _ = 1 := hnorm

/-- The low-rank Fourier-energy conclusion (5.5), for genuine binary linear
maps and genuine labeling coefficients. The spectral premise can be obtained
from the noise diagonalization; the bound is on actual restriction rank. -/
theorem labeling_lowRank_energy {Y : Type*} [Fintype Y]
    (weight : Q → ℝ) (label : Q → (E →ₗ[F2] F) → Y)
    (C : Submodule F2 F) (r : ℕ) (eigen : Q → (F →ₗ[F2] E) → ℝ) (δ : ℝ)
    (hw : ∀ q, 0 ≤ weight q) (hnorm : ∑ q, weight q = 1) (hδ : 0 ≤ δ)
    (hone : ∀ q S, eigen q S ≤ 1)
    (hhigh : ∀ q S, r < linearRankOn C S → eigen q S ≤ δ / 2)
    (hvalue : δ < spectralEnergy (fun qy : Q × Y => weight qy.1)
      (fun qy S => eigen qy.1 S) (labelingCoeff label)) :
    δ / 2 < cutoffEnergy (fun qy : Q × Y => weight qy.1)
      (fun _ S => linearRankOn C S ≤ r) (labelingCoeff label) := by
  apply cutoffEnergy_gt_half _ _ _ _ δ
  · intro qy; exact hw qy.1
  · exact hδ
  · intro qy S; exact hone qy.1 S
  · intro qy S hS; exact hhigh qy.1 S (Nat.lt_of_not_ge hS)
  · exact labelingCoeff_energy_one weight label hnorm
  · exact hvalue

end LinearMaps

section DependentLinearMaps

open MatrixCharacters MatrixFourier

variable {J : Type*} [Fintype J] {E : J → Type*} {F : Type*}
    [∀ j, AddCommGroup (E j)] [∀ j, Module F2 (E j)]
    [AddCommGroup F] [Module F2 F]
    [∀ j, FiniteDimensional F2 (E j)] [FiniteDimensional F2 F]
    [∀ j, Fintype (E j →ₗ[F2] F)] [∀ j, Fintype (F →ₗ[F2] E j)]

theorem dependent_linear_energy_parseval
    (weight : J → ℝ) (H : (j : J) → (E j →ₗ[F2] F) → ℝ) :
    energy weight (fun j S => linearCoeff (H j) S) =
      ∑ j, weight j * (𝔼 X, H j X ^ 2) := by
  unfold energy
  apply Finset.sum_congr rfl
  intro j _
  rw [linear_parseval]

omit [∀ j, FiniteDimensional F2 (E j)] [FiniteDimensional F2 F] in

theorem dependent_remainder_cutoff_le_eighth
    (weight : J → ℝ) (C : Submodule F2 F) (r : ℕ)
    (G : (j : J) → (E j →ₗ[F2] F) → ℝ) (κ δ : ℝ)
    (hw : ∀ j, 0 ≤ weight j) (hκ : 0 ≤ κ) (hκδ : κ ≤ δ / 8)
    (hlevel : ∀ j, (∑ S : F →ₗ[F2] E j,
      if linearRankOn C S ≤ r then linearCoeff (G j) S ^ 2 else 0) ≤
        κ * (𝔼 X, G j X ^ 2))
    (hmass : (∑ j, weight j * (𝔼 X, G j X ^ 2)) ≤ 1) :
    cutoffEnergy weight (fun _ S => linearRankOn C S ≤ r)
      (fun j S => linearCoeff (G j) S) ≤ δ / 8 := by
  classical
  have hs : cutoffEnergy weight (fun _ S => linearRankOn C S ≤ r)
      (fun j S => linearCoeff (G j) S) ≤
      κ * (∑ j, weight j * (𝔼 X, G j X ^ 2)) := by
    calc
      _ ≤ ∑ j, weight j * (κ * (𝔼 X, G j X ^ 2)) := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (hw j)
        simpa using hlevel j
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hm := mul_le_mul_of_nonneg_left hmass hκ
  linarith

/-- The actual removed probability energy in Section 5.3, allowing the map
domain to depend on the complete question and color index. -/
theorem dependent_deleted_energy_from_level
    (weight : J → ℝ) (C : Submodule F2 F) (r : ℕ)
    (H G : (j : J) → (E j →ₗ[F2] F) → ℝ) (κ δ : ℝ)
    (hw : ∀ j, 0 ≤ weight j) (hκ : 0 ≤ κ) (hκδ : κ ≤ δ / 8)
    (hlarge : δ / 2 < cutoffEnergy weight (fun _ S => linearRankOn C S ≤ r)
      (fun j S => linearCoeff (H j) S))
    (hlevel : ∀ j, (∑ S : F →ₗ[F2] E j,
      if linearRankOn C S ≤ r then linearCoeff (G j) S ^ 2 else 0) ≤
        κ * (𝔼 X, G j X ^ 2))
    (hmass : (∑ j, weight j * (𝔼 X, G j X ^ 2)) ≤ 1) :
    δ / 8 < ∑ j, weight j * (𝔼 X, (H j X - G j X) ^ 2) := by
  have hsmall := dependent_remainder_cutoff_le_eighth weight C r G κ δ
    hw hκ hκδ hlevel hmass
  have h := deleted_energy_gt_eighth weight (fun _ S => linearRankOn C S ≤ r)
    (fun j S => linearCoeff (H j) S) (fun j S => linearCoeff (G j) S)
    δ hw hlarge hsmall
  simpa only [← linearCoeff_sub, energy, linear_parseval, Pi.sub_apply] using h

end DependentLinearMaps

/-- Real value of a Boolean indicator. -/
def boolReal (b : Bool) : ℝ := if b then 1 else 0

@[simp] theorem boolReal_sq (b : Bool) : boolReal b ^ 2 = boolReal b := by
  cases b <;> norm_num [boolReal]

theorem boolReal_le_one (b : Bool) : boolReal b ≤ 1 := by
  cases b <;> norm_num [boolReal]

/-- Boolean indicator of one color of a labeling. -/
noncomputable def labelBool {X Y : Type*} (label : X → Y) (y : Y) : X → Bool := by
  classical
  exact fun x => decide (label x = y)

theorem labelBool_real {X Y : Type*} (label : X → Y) (y : Y) (x : X) :
    boolReal (labelBool label y x) = colorIndicator label y x := by
  classical
  simp [boolReal, labelBool, colorIndicator]

/-- Deletion's actual Boolean removed function is exactly the difference of
the original and remainder indicators. -/
theorem removed_boolReal {X Row Witness : Type*}
    (S : Deletion.RestrictionSystem X Row Witness) (H : X → Bool) (p d : ℕ) (x : X) :
    boolReal (Deletion.removed S H p d x) =
      boolReal (H x) - boolReal (Deletion.remainder S H p d x) := by
  classical
  by_cases hd : Deletion.DeletedSet S H p d x
  · simp [Deletion.removed, Deletion.remainder, hd, boolReal]
  · simp [Deletion.removed, Deletion.remainder, hd, boolReal]

theorem removed_difference_sq {X Row Witness : Type*}
    (S : Deletion.RestrictionSystem X Row Witness) (H : X → Bool) (p d : ℕ) (x : X) :
    (boolReal (H x) - boolReal (Deletion.remainder S H p d x)) ^ 2 =
      boolReal (Deletion.removed S H p d x) := by
  rw [← removed_boolReal, boolReal_sq]

section QuestionProbabilities

variable {Ω : Q → Type*} [∀ q, Fintype (Ω q)]
variable {Y A : Type*} [Fintype Y] [Fintype A]

/-- An event probability: first sample the question with the supplied weights,
then sample uniformly in its own finite space. -/
noncomputable def questionEventMass
    (weight : Q → ℝ) (B : (q : Q) → Ω q → Prop) : ℝ := by
  classical
  exact ∑ q, weight q * (𝔼 X, if B q X then (1 : ℝ) else 0)

theorem dependent_removed_union_bound
    (weight : Q → ℝ) (d : (q : Q) → Y → Ω q → ℝ)
    (B : (q : Q) → Y → A → Ω q → Prop)
    (hw : ∀ q, 0 ≤ weight q)
    (hd : ∀ q y X, d q y X ≤ 1)
    (hc : ∀ q y X, 0 < d q y X → ∃ a, B q y a X) :
    (∑ q, weight q * ∑ y, 𝔼 X, d q y X) ≤
      ∑ ya : Y × A, questionEventMass weight (fun q X => B q ya.1 ya.2 X) := by
  classical
  have hp (q : Q) (y : Y) (X : Ω q) :
      d q y X ≤ ∑ a, if B q y a X then (1 : ℝ) else 0 := by
    by_cases hpos : 0 < d q y X
    · obtain ⟨a, ha⟩ := hc q y X hpos
      have hi := Finset.single_le_sum (s := Finset.univ)
        (f := fun b : A => if B q y b X then (1 : ℝ) else 0)
        (fun b _ => by split_ifs <;> norm_num) (Finset.mem_univ a)
      exact le_trans (hd q y X) (by simpa [ha] using hi)
    · exact le_trans (le_of_not_gt hpos)
        (Finset.sum_nonneg (by intro a _; split_ifs <;> norm_num))
  calc
    _ ≤ ∑ q, weight q * ∑ y, 𝔼 X,
        ∑ a, if B q y a X then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro q _
      apply mul_le_mul_of_nonneg_left _ (hw q)
      apply Finset.sum_le_sum
      intro y _
      exact Finset.expect_le_expect (fun X _ => hp q y X)
    _ = _ := by
      simp only [questionEventMass, Finset.expect_sum_comm,
        Finset.mul_sum, Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      exact Finset.sum_comm

/-- One target is fixed before sampling the question and its map. -/
theorem fixed_target_of_removed_mass
    (weight : Q → ℝ) (d : (q : Q) → Y → Ω q → ℝ)
    (B : (q : Q) → Y → A → Ω q → Prop)
    (hw : ∀ q, 0 ≤ weight q) (hd : ∀ q y X, d q y X ≤ 1)
    (hc : ∀ q y X, 0 < d q y X → ∃ a, B q y a X)
    (δ : ℝ) (N : ℕ) (hδ : 0 ≤ δ) (hN : 0 < N)
    (hcount : Fintype.card (Y × A) ≤ N)
    (hremoved : δ / 8 < ∑ q, weight q * ∑ y, 𝔼 X, d q y X) :
    ∃ y a, δ / (8 * (N : ℝ)) <
      questionEventMass weight (fun q X => B q y a X) := by
  have hu := dependent_removed_union_bound weight d B hw hd hc
  obtain ⟨⟨y, a⟩, hya⟩ := exists_fixed_event_scaled
    (fun ya : Y × A => questionEventMass weight (fun q X => B q ya.1 ya.2 X))
    N δ hN hδ hcount (lt_of_lt_of_le hremoved hu)
  exact ⟨y, a, hya⟩

/-- A Boolean subpartition has total squared mass at most one. Colors are
summed with counting measure, not averaged. -/
theorem boolean_subpartition_energy_le_one [∀ q, Nonempty (Ω q)]
    (weight : Q → ℝ) (label : (q : Q) → Ω q → Y)
    (G : (q : Q) → Y → Ω q → Bool)
    (hw : ∀ q, 0 ≤ weight q) (hnorm : ∑ q, weight q = 1)
    (hG : ∀ q y X, G q y X = true → label q X = y) :
    (∑ q, weight q * ∑ y, 𝔼 X, boolReal (G q y X) ^ 2) ≤ 1 := by
  classical
  have hp (q : Q) (X : Ω q) :
      (∑ y, boolReal (G q y X) ^ 2) ≤ 1 := by
    calc
      _ ≤ ∑ y, colorIndicator (label q) y X ^ 2 := by
        apply Finset.sum_le_sum
        intro y _
        by_cases hg : G q y X = true
        · have hl := hG q y X hg
          simp [hg, boolReal, colorIndicator, hl]
        · simpa [boolReal, hg] using sq_nonneg (colorIndicator (label q) y X)
      _ = 1 := colorIndicator_partition (label q) X
  have hq (q : Q) : (∑ y, 𝔼 X, boolReal (G q y X) ^ 2) ≤ 1 := by
    rw [← Finset.expect_sum_comm]
    calc
      _ ≤ 𝔼 _X : Ω q, (1 : ℝ) := Finset.expect_le_expect (fun X _ => hp q X)
      _ = 1 := Fintype.expect_const 1
  calc
    _ ≤ ∑ q, weight q * 1 :=
      Finset.sum_le_sum (fun q _ => mul_le_mul_of_nonneg_left (hq q) (hw q))
    _ = 1 := by simpa using hnorm

/-- The actual whole-row remainder of labeling indicators satisfies the mass
bound needed in the deleted-energy argument, with no remaining mass hypothesis. -/
theorem remainder_subpartition_energy_le_one [∀ q, Nonempty (Ω q)]
    {Row Witness : Q → Type*}
    (S : (q : Q) → Deletion.RestrictionSystem (Ω q) (Row q) (Witness q))
    (weight : Q → ℝ) (label : (q : Q) → Ω q → Y) (p d : ℕ)
    (hw : ∀ q, 0 ≤ weight q) (hnorm : ∑ q, weight q = 1) :
    (∑ q, weight q * ∑ y, 𝔼 X,
      boolReal (Deletion.remainder (S q) (labelBool (label q) y) p d X) ^ 2) ≤ 1 := by
  apply boolean_subpartition_energy_le_one weight label _ hw hnorm
  intro q y X hG
  have h := Deletion.remainder_le_original (S q) (labelBool (label q) y) p d X hG
  simpa [labelBool] using h

end QuestionProbabilities

open MatrixCharacters

variable {C : Type*} [AddCommGroup C] [Module F2 C]
    [FiniteDimensional F2 C] [Fintype C]
    {E : Q → Type*} [∀ q, AddCommGroup (E q)] [∀ q, Module F2 (E q)]
    [∀ q, Finite (E q)] [∀ q, Fintype (E q →ₗ[F2] C)]

/-- Equation (5.13) for the actual whole-row deletion system. Only the color
and target subspace are selected. Neither the question, row value, nor witness
vanishing subspace is part of the counted target. -/
theorem fixed_badRow_target_of_removed_mass
    (weight : Q → ℝ) (H : (q : Q) → C → (E q →ₗ[F2] C) → Bool)
    (r p d : ℕ) (δ : ℝ)
    (hw : ∀ q, 0 ≤ weight q) (hδ : 0 ≤ δ)
    (hremoved : δ / 8 < ∑ q, weight q * ∑ y, 𝔼 X,
      boolReal (Deletion.removed (MatrixRestrictions.system r) (H q y) p d X)) :
    ∃ (y : C) (C' : Submodule F2 C), Module.finrank F2 (C ⧸ C') ≤ r ∧
      δ / (8 * (Nat.card C : ℝ) * (2 : ℝ) ^
        (Module.finrank F2 C * Module.finrank F2 C)) <
      questionEventMass weight (fun q (X : E q →ₗ[F2] C) =>
        Deletion.BadRow (MatrixRestrictions.system r) (H q y) p d
          ⟨C', C'.mkQ.comp X⟩) := by
  classical
  let : Finite (C →ₗ[F2] C) := Finite.of_injective
    (fun f : C →ₗ[F2] C => (f : C → C)) DFunLike.coe_injective
  let : Finite (Submodule F2 C) := Finite.of_surjective
    (fun f : C →ₗ[F2] C => LinearMap.range f)
    MatrixSubspaceCount.endomorphism_range_surjective
  let A := {C' : Submodule F2 C // Module.finrank F2 (C ⧸ C') ≤ r}
  let : Fintype A := Fintype.ofFinite A
  let N := Nat.card C * 2 ^ (Module.finrank F2 C * Module.finrank F2 C)
  let value (q : Q) (y : C) (X : E q →ₗ[F2] C) : ℝ :=
    boolReal (Deletion.removed (MatrixRestrictions.system r) (H q y) p d X)
  let event (q : Q) (y : C) (a : A) (X : E q →ₗ[F2] C) : Prop :=
    Deletion.BadRow (MatrixRestrictions.system r) (H q y) p d
      ⟨a.val, a.val.mkQ.comp X⟩
  have hcover (q : Q) (y : C) (X : E q →ₗ[F2] C) (hpos : 0 < value q y X) :
      ∃ a : A, event q y a X := by
    have ht : Deletion.removed (MatrixRestrictions.system r) (H q y) p d X = true := by
      by_contra hn
      simp [value, boolReal, hn] at hpos
    have hdel : Deletion.DeletedSet (MatrixRestrictions.system r) (H q y) p d X := by
      by_contra hn
      simp [Deletion.removed, hn] at ht
    obtain ⟨C', hcodim, hbad⟩ :=
      (MatrixRestrictions.deletedSet_iff_exists_admissible_target (H q y) r p d X).mp hdel
    exact ⟨⟨C', hcodim⟩, hbad⟩
  have hcount : Fintype.card (C × A) ≤ N := by
    simpa only [A, N, Nat.card_eq_fintype_card] using
      (MatrixSubspaceCount.card_color_admissible_subspaces_le
        (fun C' : Submodule F2 C => Module.finrank F2 (C ⧸ C') ≤ r))
  have hN : 0 < N := by
    simpa only [N, Nat.card_eq_fintype_card] using
      (Nat.mul_pos (Fintype.card_pos : 0 < Fintype.card C)
        (pow_pos (by norm_num : 0 < (2 : ℕ)) (Module.finrank F2 C * Module.finrank F2 C)))
  obtain ⟨y, a, ha⟩ := fixed_target_of_removed_mass weight value event hw
    (fun _ _ _ => boolReal_le_one _) hcover δ N hδ hN hcount hremoved
  refine ⟨y, a.val, a.property, ?_⟩
  simpa only [N, event, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc] using ha

end MaxCutGames.Fourier.MatrixEnergy

end OAI
