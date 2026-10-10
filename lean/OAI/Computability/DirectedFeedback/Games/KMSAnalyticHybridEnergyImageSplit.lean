import Mathlib
import OAI.Computability.DirectedFeedback.Games.Derivatives

namespace OAI

noncomputable section

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical

variable {R B U : Type*} [Ring R]
  [AddCommGroup B] [Module R B] [AddCommGroup U] [Module R U]

theorem range_subtype_comp_of_surjective (W : Submodule R U)
    (z : B →ₗ[R] W) (hz : Function.Surjective z) :
    (W.subtype.comp z).range = W := by
  ext u
  constructor
  · rintro ⟨b, rfl⟩
    exact (z b).property
  · intro hu
    obtain ⟨b, hb⟩ := hz ⟨u, hu⟩
    exact ⟨b, congrArg Subtype.val hb⟩

def fixedImageEquivSurjection (W : Submodule R U) :
    {z : B →ₗ[R] U // z.range = W} ≃
      {z : B →ₗ[R] W // Function.Surjective z} where
  toFun z := ⟨z.val.codRestrict W (fun b => z.property.le (LinearMap.mem_range_self z.val b)), by
    intro w
    have hw : w.val ∈ z.val.range := z.property.symm ▸ w.property
    obtain ⟨b, hb⟩ := hw
    exact ⟨b, Subtype.ext hb⟩⟩
  invFun z := ⟨W.subtype.comp z.val, range_subtype_comp_of_surjective W z.val z.property⟩
  left_inv z := by
    apply Subtype.ext
    apply LinearMap.ext
    intro b
    rfl
  right_inv z := by
    apply Subtype.ext
    apply LinearMap.ext
    intro b
    apply Subtype.ext
    rfl

@[simp] theorem fixedImageEquivSurjection_symm_val (W : Submodule R U)
    (z : {z : B →ₗ[R] W // Function.Surjective z}) :
    ((fixedImageEquivSurjection W).symm z).val = W.subtype.comp z.val := rfl

@[simp] theorem fixedImageEquivSurjection_apply_coe (W : Submodule R U)
    (z : {z : B →ₗ[R] U // z.range = W}) (b : B) :
    ((fixedImageEquivSurjection W z).val b : U) = z.val b := rfl

abbrev ImageRankFrequency (q : ℕ) :=
  {z : B →ₗ[R] U // Module.finrank R z.range = q}

abbrev RankImage (R U : Type*) [Ring R] [AddCommGroup U] [Module R U] (q : ℕ) :=
  {W : Submodule R U // Module.finrank R W = q}

def frequencyImage (q : ℕ) (z : ImageRankFrequency (R := R) (B := B) (U := U) q) :
    RankImage R U q := ⟨z.val.range, z.property⟩

def frequencyImageFiberEquiv (q : ℕ) (W : RankImage R U q) :
    {z : ImageRankFrequency (R := R) (B := B) (U := U) q // frequencyImage q z = W} ≃
      {z : B →ₗ[R] U // z.range = W.val} where
  toFun z := ⟨z.val.val, congrArg Subtype.val z.property⟩
  invFun z := ⟨⟨z.val, by rw [z.property]; exact W.property⟩, Subtype.ext z.property⟩
  left_inv z := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv z := by apply Subtype.ext; rfl

def rankFrequencyImageEquiv (q : ℕ) :
    ImageRankFrequency (R := R) (B := B) (U := U) q ≃
      Σ W : RankImage R U q, {z : B →ₗ[R] W.val // Function.Surjective z} :=
  (Equiv.sigmaFiberEquiv (frequencyImage (R := R) (B := B) (U := U) q)).symm.trans
    (Equiv.sigmaCongrRight fun W =>
      (frequencyImageFiberEquiv q W).trans (fixedImageEquivSurjection W.val))

@[simp] theorem rankFrequencyImageEquiv_symm_val (q : ℕ)
    (p : Σ W : RankImage R U q, {z : B →ₗ[R] W.val // Function.Surjective z}) :
    ((rankFrequencyImageEquiv q).symm p).val = p.1.val.subtype.comp p.2.val := rfl

section Sums

variable [Fintype (B →ₗ[R] U)] [Fintype (Submodule R U)]
  [∀ W : Submodule R U, Fintype (B →ₗ[R] W)]

omit [Fintype (Submodule R U)] in

theorem sum_fixedImage_eq_sum_surjection (W : Submodule R U)
    (weight : (B →ₗ[R] U) → ℝ) :
    (∑ z : {z : B →ₗ[R] U // z.range = W}, weight z.val) =
      ∑ z : {z : B →ₗ[R] W // Function.Surjective z}, weight (W.subtype.comp z.val) := by
  symm
  apply Fintype.sum_equiv (fixedImageEquivSurjection W).symm
  intro z
  rfl

theorem sum_rankFrequency_eq_sum_image (q : ℕ) (weight : (B →ₗ[R] U) → ℝ) :
    (∑ z : ImageRankFrequency (R := R) (B := B) (U := U) q, weight z.val) =
      ∑ W : RankImage R U q,
        ∑ z : {z : B →ₗ[R] W.val // Function.Surjective z},
          weight (W.val.subtype.comp z.val) := by
  calc
    _ = ∑ p : Σ W : RankImage R U q,
        {z : B →ₗ[R] W.val // Function.Surjective z},
        weight (p.1.val.subtype.comp p.2.val) := by
      symm
      apply Fintype.sum_equiv (rankFrequencyImageEquiv q).symm
      intro p
      rfl
    _ = _ := Fintype.sum_sigma _

theorem sum_filter_rank_eq_sum_image (q : ℕ) (weight : (B →ₗ[R] U) → ℝ) :
    (∑ z : B →ₗ[R] U with Module.finrank R z.range = q, weight z) =
      ∑ W : RankImage R U q,
        ∑ z : {z : B →ₗ[R] W.val // Function.Surjective z},
          weight (W.val.subtype.comp z.val) := by
  rw [Finset.sum_subtype (p := fun z : B →ₗ[R] U => Module.finrank R z.range = q)
    (Finset.univ.filter fun z : B →ₗ[R] U =>
    Module.finrank R z.range = q) (by simp) weight]
  exact sum_rankFrequency_eq_sum_image q weight

theorem sum_eq_sum_image_of_rank_support (q : ℕ) (weight : (B →ₗ[R] U) → ℝ)
    (hsupport : ∀ z, Module.finrank R z.range ≠ q → weight z = 0) :
    (∑ z : B →ₗ[R] U, weight z) =
      ∑ W : RankImage R U q,
        ∑ z : {z : B →ₗ[R] W.val // Function.Surjective z},
          weight (W.val.subtype.comp z.val) := by
  rw [← sum_filter_rank_eq_sum_image, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : Module.finrank R z.range = q
  · simp [hz]
  · simp [hz, hsupport z hz]

end Sums

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def imageCoordinates (W D : Submodule K V) (h : IsCompl W D) : V ≃ₗ[K] (W × D) :=
  (Submodule.prodEquivOfIsCompl W D h).symm

@[simp] theorem imageCoordinates_subtype (W D : Submodule K V) (h : IsCompl W D)
    (w : W) : imageCoordinates W D h (w : V) = (w, 0) :=
  Submodule.prodEquivOfIsCompl_symm_apply_left W D h w

theorem imageCoordinates_frequency {X : Type*} [AddCommGroup X] [Module K X]
    (W D : Submodule K V) (h : IsCompl W D) (z : X →ₗ[K] W) :
    (imageCoordinates W D h).toLinearMap.comp (W.subtype.comp z) =
      z.prod (0 : X →ₗ[K] D) := by
  apply LinearMap.ext
  intro x
  exact imageCoordinates_subtype W D h (z x)

theorem imageCoordinates_finrank [FiniteDimensional K V]
    (W D : Submodule K V) (h : IsCompl W D) :
    Module.finrank K W + Module.finrank K D = Module.finrank K V := by
  simpa only [Module.finrank_prod] using (Submodule.prodEquivOfIsCompl W D h).finrank_eq

theorem exists_imageCoordinates (W : Submodule K V) :
    ∃ D : Submodule K V, ∃ e : V ≃ₗ[K] (W × D), ∀ w : W, e (w : V) = (w, 0) := by
  obtain ⟨D, h⟩ := W.exists_isCompl
  exact ⟨D, imageCoordinates W D h, imageCoordinates_subtype W D h⟩

end DFVSGames.Inverse.KMSAnalyticHybridEnergy

end

namespace DFVSGames.Inverse.KMSAnalyticHybridCoordinates

variable {R A W D B C : Type*} [Ring R]
  [AddCommGroup A] [Module R A] [AddCommGroup W] [Module R W]
  [AddCommGroup D] [Module R D] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

def compressBlock (S : (B × C) →ₗ[R] (A × (W × D))) : B →ₗ[R] (W × D) :=
  (LinearMap.snd R A (W × D)).comp (S.comp (LinearMap.inl R B C))

@[simp] theorem compressBlock_apply
    (S : (B × C) →ₗ[R] (A × (W × D))) (b : B) :
    compressBlock S b = (S (b, 0)).2 := rfl

structure Coordinates (z : B →ₗ[R] W) where
  alpha : (B × C) →ₗ[R] A
  psi : (B × C) →ₗ[R] W
  psi_left : psi.comp (LinearMap.inl R B C) = z
  v : C →ₗ[R] D

@[ext] theorem Coordinates.ext {z : B →ₗ[R] W} {p q : Coordinates (A := A) (D := D)
    (C := C) z} (ha : p.alpha = q.alpha) (hp : p.psi = q.psi) (hv : p.v = q.v) : p = q := by
  cases p
  cases q
  cases ha
  cases hp
  cases hv
  rfl

def assemble {z : B →ₗ[R] W} (p : Coordinates (A := A) (D := D) (C := C) z) :
    (B × C) →ₗ[R] (A × (W × D)) :=
  p.alpha.prod (p.psi.prod (p.v.comp (LinearMap.snd R B C)))

@[simp] theorem assemble_apply {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z) (x : B × C) :
    assemble p x = (p.alpha x, p.psi x, p.v x.2) := rfl

@[simp] theorem compressBlock_assemble {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z) :
    compressBlock (assemble p) = z.prod (0 : B →ₗ[R] D) := by
  apply LinearMap.ext
  intro b
  have hp : p.psi (b, 0) = z b :=
    congrArg (fun L : (B →ₗ[R] W) => L b) p.psi_left
  simp [compressBlock, assemble, hp]

def extract (z : B →ₗ[R] W)
    (S : {S : (B × C) →ₗ[R] (A × (W × D)) //
      compressBlock S = z.prod (0 : B →ₗ[R] D)}) :
    Coordinates (A := A) (D := D) (C := C) z where
  alpha := (LinearMap.fst R A (W × D)).comp S.val
  psi := (LinearMap.fst R W D).comp ((LinearMap.snd R A (W × D)).comp S.val)
  psi_left := by
    apply LinearMap.ext
    intro b
    exact congrArg (fun L : B →ₗ[R] (W × D) => (L b).1) S.property
  v := (LinearMap.snd R W D).comp
    ((LinearMap.snd R A (W × D)).comp (S.val.comp (LinearMap.inr R B C)))

@[simp] theorem assemble_extract (z : B →ₗ[R] W)
    (S : {S : (B × C) →ₗ[R] (A × (W × D)) //
      compressBlock S = z.prod (0 : B →ₗ[R] D)}) :
    assemble (extract z S) = S.val := by
  apply LinearMap.ext
  rintro ⟨b, c⟩
  have hzero : (S.val (b, 0)).2.2 = 0 :=
    congrArg (fun L : B →ₗ[R] (W × D) => (L b).2) S.property
  have hlast : (S.val (b, c)).2.2 = (S.val (0, c)).2.2 := by
    calc
      _ = (S.val ((b, 0) + (0, c))).2.2 := by simp
      _ = (S.val (b, 0)).2.2 + (S.val (0, c)).2.2 := by rw [map_add]; rfl
      _ = _ := by rw [hzero, zero_add]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · exact hlast.symm

@[simp] theorem extract_assemble {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z) :
    extract z ⟨assemble p, compressBlock_assemble p⟩ = p := by
  apply Coordinates.ext
  · apply LinearMap.ext
    intro x
    rfl
  · apply LinearMap.ext
    intro x
    rfl
  · apply LinearMap.ext
    intro c
    rfl

def compressedFiberEquiv (z : B →ₗ[R] W) :
    {S : (B × C) →ₗ[R] (A × (W × D)) //
      compressBlock S = z.prod (0 : B →ₗ[R] D)} ≃
      Coordinates (A := A) (D := D) (C := C) z where
  toFun := extract z
  invFun p := ⟨assemble p, compressBlock_assemble p⟩
  left_inv S := Subtype.ext (assemble_extract z S)
  right_inv := extract_assemble

theorem assemble_injective (z : B →ₗ[R] W) :
    Function.Injective (assemble (R := R) (A := A) (D := D) (C := C) (z := z)) := by
  intro p q h
  have hh : (compressedFiberEquiv (A := A) (D := D) (C := C) z).symm p =
      (compressedFiberEquiv (A := A) (D := D) (C := C) z).symm q := Subtype.ext h
  exact (compressedFiberEquiv (A := A) (D := D) (C := C) z).symm.injective hh

end DFVSGames.Inverse.KMSAnalyticHybridCoordinates

namespace DFVSGames.Inverse.KMSAnalyticHybridCoordinates

variable {R A W D B C : Type*} [Field R]
  [AddCommGroup A] [Module R A] [AddCommGroup W] [Module R W]
  [AddCommGroup D] [Module R D] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

open DFVSGames.Appendix

private theorem psi_split_inline_KMSAnalyticHybridCoordinatesConditions {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z) (b : B) (c : C) :
    p.psi (b, c) = z b + p.psi (0, c) := by
  have hleft : p.psi (b, 0) = z b :=
    congrArg (fun L : B →ₗ[R] W => L b) p.psi_left
  calc
    p.psi (b, c) = p.psi ((b, 0) + (0, c)) := by simp
    _ = p.psi (b, 0) + p.psi (0, c) := p.psi.map_add _ _
    _ = z b + p.psi (0, c) := by rw [hleft]

theorem hybrid_assemble_iff {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z)
    (hz : Function.Surjective z) :
    LinearIdentities.Hybrid (assemble p)
        (LinearMap.range (LinearMap.inl R A (W × D)))
        (LinearMap.range (LinearMap.inl R B C)) ↔
      Function.Injective p.v ∧
        Function.Surjective (p.alpha.prod (p.psi.prod (LinearMap.snd R B C))) := by
  constructor
  · intro h
    have hzero : ∀ c : C, p.v c = 0 → c = 0 := by
      intro c hc
      obtain ⟨b, hb⟩ := hz (-p.psi (0, c))
      have hpsi : p.psi (b, c) = 0 := by
        rw [psi_split_inline_KMSAnalyticHybridCoordinatesConditions, hb, neg_add_cancel]
      have hmem : (b, c) ∈ LinearMap.range (LinearMap.inl R B C) := by
        apply h.2
        change assemble p (b, c) ∈ LinearMap.range (LinearMap.inl R A (W × D))
        refine ⟨p.alpha (b, c), ?_⟩
        change (p.alpha (b, c), (0, 0)) = (p.alpha (b, c), p.psi (b, c), p.v c)
        rw [hpsi, hc]
      obtain ⟨b', hb'⟩ := hmem
      exact (congrArg (fun x : B × C => x.2) hb').symm
    refine ⟨?_, ?_⟩
    · intro c d hcd
      apply sub_eq_zero.mp
      apply hzero
      rw [map_sub, hcd, sub_self]
    · rintro ⟨a, w, c⟩
      obtain ⟨b, hb⟩ := hz (w - p.psi (0, c))
      have hpsi : p.psi (b, c) = w := by
        rw [psi_split_inline_KMSAnalyticHybridCoordinatesConditions, hb, sub_add_cancel]
      have hmem : (a - p.alpha (b, c), (0, 0)) ∈ LinearMap.range (assemble p) := by
        apply h.1
        exact ⟨a - p.alpha (b, c), rfl⟩
      obtain ⟨x, hx⟩ := hmem
      have hxa : p.alpha x = a - p.alpha (b, c) :=
        congrArg (fun y : A × (W × D) => y.1) hx
      have hxw : p.psi x = 0 :=
        congrArg (fun y : A × (W × D) => y.2.1) hx
      have hxd : p.v x.2 = 0 :=
        congrArg (fun y : A × (W × D) => y.2.2) hx
      have hxc : x.2 = 0 := hzero _ hxd
      refine ⟨x + (b, c), ?_⟩
      change (p.alpha (x + (b, c)), p.psi (x + (b, c)), (x + (b, c)).2) =
        (a, w, c)
      apply Prod.ext
      · rw [map_add, hxa, sub_add_cancel]
      · apply Prod.ext
        · change p.psi (x + (b, c)) = w
          rw [map_add, hxw, zero_add, hpsi]
        · change x.2 + c = c
          rw [hxc, zero_add]
  · rintro ⟨hv, htheta⟩
    constructor
    · rintro y ⟨a, rfl⟩
      obtain ⟨x, hx⟩ := htheta (a, 0, 0)
      change (p.alpha x, p.psi x, x.2) = (a, 0, 0) at hx
      have hxa : p.alpha x = a := congrArg (fun y : A × (W × C) => y.1) hx
      have hxw : p.psi x = 0 := congrArg (fun y : A × (W × C) => y.2.1) hx
      have hxc : x.2 = 0 := congrArg (fun y : A × (W × C) => y.2.2) hx
      refine ⟨x, ?_⟩
      change (p.alpha x, p.psi x, p.v x.2) = (a, 0, 0)
      rw [hxa, hxw, hxc, map_zero]
    · intro x hx
      change assemble p x ∈ LinearMap.range (LinearMap.inl R A (W × D)) at hx
      obtain ⟨a, ha⟩ := hx
      have hxd : p.v x.2 = 0 :=
        (congrArg (fun y : A × (W × D) => y.2.2) ha).symm
      have hxc : x.2 = 0 := hv (by simpa only [map_zero] using hxd)
      exact ⟨x.1, Prod.ext rfl hxc.symm⟩

end DFVSGames.Inverse.KMSAnalyticHybridCoordinates

namespace DFVSGames.Inverse.KMSAnalyticHybridCoordinates

variable {R A W D B C : Type*} [Ring R]
  [AddCommGroup A] [Module R A] [AddCommGroup W] [Module R W]
  [AddCommGroup D] [Module R D] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

def fullCoordinates {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z) :
    (B × C) →ₗ[R] (A × (W × C)) :=
  p.alpha.prod (p.psi.prod (LinearMap.snd R B C))

def embedLast (v : C →ₗ[R] D) : (A × (W × C)) →ₗ[R] (A × (W × D)) :=
  (LinearMap.id : A →ₗ[R] A).prodMap ((LinearMap.id : W →ₗ[R] W).prodMap v)

@[simp] theorem embedLast_apply (v : C →ₗ[R] D) (x : A × (W × C)) :
    embedLast v x = (x.1, x.2.1, v x.2.2) := rfl

theorem embedLast_injective (v : C →ₗ[R] D) (hv : Function.Injective v) :
    Function.Injective (embedLast (A := A) (W := W) v) := by
  intro x y h
  apply Prod.ext
  · exact congrArg (fun u : A × (W × D) => u.1) h
  · apply Prod.ext
    · exact congrArg (fun u : A × (W × D) => u.2.1) h
    · apply hv
      exact congrArg (fun u : A × (W × D) => u.2.2) h

theorem assemble_eq_embedLast_comp {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z) :
    assemble p = (embedLast p.v).comp (fullCoordinates p) := by
  apply LinearMap.ext
  intro x
  rfl

theorem range_assemble_of_fullCoordinates_surjective {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z)
    (hp : Function.Surjective (fullCoordinates p)) :
    (assemble p).range = (embedLast (A := A) (W := W) p.v).range := by
  rw [assemble_eq_embedLast_comp, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr hp, Submodule.map_top]

theorem finrank_assemble {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z)
    (hv : Function.Injective p.v) (hp : Function.Surjective (fullCoordinates p)) :
    Module.finrank R (assemble p).range = Module.finrank R (A × (W × C)) := by
  rw [range_assemble_of_fullCoordinates_surjective p hp]
  exact LinearMap.finrank_range_of_inj (embedLast_injective p.v hv)

theorem ker_assemble {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z)
    (hv : Function.Injective p.v) :
    (assemble p).ker = (fullCoordinates p).ker := by
  rw [assemble_eq_embedLast_comp]
  exact LinearMap.ker_comp_of_ker_eq_bot _
    (LinearMap.ker_eq_bot.mpr (embedLast_injective p.v hv))

end DFVSGames.Inverse.KMSAnalyticHybridCoordinates

namespace DFVSGames.Inverse.KMSAnalyticHybridCoordinates

variable {R A W D B C : Type*} [Field R]
  [AddCommGroup A] [Module R A] [AddCommGroup W] [Module R W]
  [AddCommGroup D] [Module R D] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

open DFVSGames.Appendix

def hybridFiberEquiv (z : B →ₗ[R] W) (hz : Function.Surjective z) :
    {S : (B × C) →ₗ[R] (A × (W × D)) //
      compressBlock S = z.prod (0 : B →ₗ[R] D) ∧
        LinearIdentities.Hybrid S
          (LinearMap.range (LinearMap.inl R A (W × D)))
          (LinearMap.range (LinearMap.inl R B C))} ≃
      {p : Coordinates (A := A) (D := D) (C := C) z //
        Function.Injective p.v ∧ Function.Surjective (fullCoordinates p)} where
  toFun S := ⟨extract z ⟨S.val, S.property.1⟩, by
    apply (hybrid_assemble_iff _ hz).mp
    rw [assemble_extract]
    exact S.property.2⟩
  invFun p := ⟨assemble p.val, compressBlock_assemble p.val,
    (hybrid_assemble_iff p.val hz).mpr p.property⟩
  left_inv S := by
    apply Subtype.ext
    exact assemble_extract z ⟨S.val, S.property.1⟩
  right_inv p := by
    apply Subtype.ext
    exact extract_assemble p.val

theorem hybridFiber_finrank (z : B →ₗ[R] W) (hz : Function.Surjective z)
    (S : (B × C) →ₗ[R] (A × (W × D)))
    (hc : compressBlock S = z.prod (0 : B →ₗ[R] D))
    (hh : LinearIdentities.Hybrid S
      (LinearMap.range (LinearMap.inl R A (W × D)))
      (LinearMap.range (LinearMap.inl R B C))) :
    Module.finrank R S.range = Module.finrank R (A × (W × C)) := by
  let p := (hybridFiberEquiv (A := A) (D := D) (C := C) z hz) ⟨S, hc, hh⟩
  have he : assemble p.val = S := assemble_extract z ⟨S, hc⟩
  rw [← he]
  exact finrank_assemble p.val p.property.1 p.property.2

end DFVSGames.Inverse.KMSAnalyticHybridCoordinates

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier

variable {E F I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]

def smallCoeff (ι : I →ₗ[F2] E) (f : (E →ₗ[F2] F) → ℝ)
    (T : F →ₗ[F2] I) : ℝ :=
  if Function.Surjective T then linearCoeff f (ι.comp T) else 0

def smallComponent (ι : I →ₗ[F2] E) (f : (E →ₗ[F2] F) → ℝ) :
    (I →ₗ[F2] F) → ℝ := synthesis (smallCoeff ι f)

omit [FiniteDimensional F2 E] [Fintype (F →ₗ[F2] E)] in
@[simp] theorem coeff_smallComponent (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (T : F →ₗ[F2] I) :
    linearCoeff (smallComponent ι f) T = smallCoeff ι f T :=
  coeff_synthesis _ _

omit [FiniteDimensional F2 E] [Fintype (F →ₗ[F2] E)] in
theorem coeff_smallComponent_of_surjective (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (T : F →ₗ[F2] I)
    (hT : Function.Surjective T) :
    linearCoeff (smallComponent ι f) T = linearCoeff f (ι.comp T) := by
  simp only [coeff_smallComponent, smallCoeff, ite_eq_left hT]

omit [FiniteDimensional F2 E] [Fintype (F →ₗ[F2] E)] in
theorem coeff_smallComponent_of_not_surjective (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (T : F →ₗ[F2] I)
    (hT : ¬ Function.Surjective T) : linearCoeff (smallComponent ι f) T = 0 := by
  simp only [coeff_smallComponent, smallCoeff, ite_eq_right hT]

omit [FiniteDimensional F2 E] [Fintype (F →ₗ[F2] E)] in

theorem smallComponent_energy (ι : I →ₗ[F2] E) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, smallComponent ι f X ^ 2) =
      ∑ T ∈ Finset.univ.filter (fun T : F →ₗ[F2] I => Function.Surjective T),
        linearCoeff f (ι.comp T) ^ 2 := by
  rw [smallComponent, synthesis_energy, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hT : Function.Surjective T <;> simp [smallCoeff, hT]

omit [FiniteDimensional F2 E] [Fintype (F →ₗ[F2] E)] in

theorem rankComponent_smallComponent (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) :
    rankComponent (Module.finrank F2 I) (smallComponent ι f) = smallComponent ι f := by
  apply eq_of_coeff_eq
  intro T
  simp only [rankComponent, coeff_component, coeff_smallComponent]
  by_cases hT : Function.Surjective T
  · have hr : Module.finrank F2 T.range = Module.finrank F2 I :=
      Submodule.eq_top_iff_finrank_eq.mp (LinearMap.range_eq_top.mpr hT)
    simp [hr]
  · simp [smallCoeff, hT]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)] in

theorem ker_comp_of_injective (ι : I →ₗ[F2] E) (hι : Function.Injective ι)
    (T : F →ₗ[F2] I) : (ι.comp T).ker = T.ker :=
  LinearMap.ker_comp_of_ker_eq_bot T (LinearMap.ker_eq_bot.mpr hι)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I] [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)] in

theorem smallCoeff_eq_of_kernel_coeff_const (ι κ : I →ₗ[F2] E)
    (hι : Function.Injective ι) (hκ : Function.Injective κ)
    (f : (E →ₗ[F2] F) → ℝ)
    (hcoeff : ∀ S T : F →ₗ[F2] E,
      S.ker = T.ker → linearCoeff f S = linearCoeff f T) :
    smallCoeff ι f = smallCoeff κ f := by
  funext T
  unfold smallCoeff
  by_cases hT : Function.Surjective T
  · simp only [ite_eq_left hT]
    exact hcoeff _ _ ((ker_comp_of_injective ι hι T).trans
      (ker_comp_of_injective κ hκ T).symm)
  · simp only [ite_eq_right hT]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] in
theorem smallComponent_eq_of_kernel_coeff_const (ι κ : I →ₗ[F2] E)
    (hι : Function.Injective ι) (hκ : Function.Injective κ)
    (f : (E →ₗ[F2] F) → ℝ)
    (hcoeff : ∀ S T : F →ₗ[F2] E,
      S.ker = T.ker → linearCoeff f S = linearCoeff f T) :
    smallComponent ι f = smallComponent κ f :=
  congrArg synthesis (smallCoeff_eq_of_kernel_coeff_const ι κ hι hκ f hcoeff)

omit [FiniteDimensional F2 E] [Fintype (F →ₗ[F2] E)] in

theorem smallComponent_orthogonal (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (g : (I →ₗ[F2] F) → ℝ)
    (hg : ∀ T : F →ₗ[F2] I, Function.Surjective T → linearCoeff g T = 0) :
    (𝔼 X, smallComponent ι f X * g X) = 0 := by
  rw [← linear_parseval_inner]
  apply Finset.sum_eq_zero
  intro T _
  rw [coeff_smallComponent]
  by_cases hT : Function.Surjective T
  · rw [hg T hT, mul_zero]
  · simp [smallCoeff, hT]

theorem smallComponent_energy_le (ι : I →ₗ[F2] E) (hι : Function.Injective ι)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, smallComponent ι f X ^ 2) ≤ 𝔼 X, f X ^ 2 := by
  have hinj : Function.Injective (fun T : F →ₗ[F2] I => ι.comp T) := by
    intro T U hTU
    apply LinearMap.ext
    intro x
    apply hι
    exact congrArg (fun S : F →ₗ[F2] E => S x) hTU
  rw [smallComponent_energy, ← linear_parseval]
  calc
    _ = ∑ S ∈ (Finset.univ.filter (fun T : F →ₗ[F2] I => Function.Surjective T)).image
        (fun T => ι.comp T), linearCoeff f S ^ 2 := by
      rw [Finset.sum_image]
      intro T _ U _ hTU
      exact hinj hTU
    _ ≤ ∑ S, linearCoeff f S ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun S _ _ => sq_nonneg _)

end
end DFVSGames.Inverse.KMSAnalytic

namespace DFVSGames.Inverse.KMSKernelOrbits

noncomputable section

variable {K E F : Type*} [DivisionRing K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

def rangeEquivOfKerEq (S T : F →ₗ[K] E) (hker : S.ker = T.ker) :
    S.range ≃ₗ[K] T.range :=
  S.quotKerEquivRange.symm ≪≫ₗ
    Submodule.quotEquivOfEq S.ker T.ker hker ≪≫ₗ T.quotKerEquivRange

theorem rangeEquivOfKerEq_apply (S T : F →ₗ[K] E) (hker : S.ker = T.ker) (x : F) :
    (rangeEquivOfKerEq S T hker ⟨S x, ⟨x, rfl⟩⟩ : E) = T x := by
  change (T.quotKerEquivRange ((Submodule.quotEquivOfEq S.ker T.ker hker)
    (S.quotKerEquivRange.symm ⟨S x, ⟨x, rfl⟩⟩)) : E) = T x
  have hs : (⟨S x, ⟨x, rfl⟩⟩ : S.range) =
      S.quotKerEquivRange (Submodule.Quotient.mk x) := rfl
  rw [hs, LinearEquiv.symm_apply_apply]
  rfl

theorem exists_postcomp_equiv_of_ker_eq (S T : F →ₗ[K] E)
    [FiniteDimensional K S.range] (hker : S.ker = T.ker) :
    ∃ g : E ≃ₗ[K] E, g.toLinearMap.comp S = T := by
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq
    (rangeEquivOfKerEq S T hker)
  refine ⟨g, ?_⟩
  ext x
  change g (S x) = T x
  exact (hg ⟨S x, ⟨x, rfl⟩⟩).symm.trans (rangeEquivOfKerEq_apply S T hker x)

theorem ker_eq_iff_exists_postcomp_equiv (S T : F →ₗ[K] E)
    [FiniteDimensional K S.range] :
    S.ker = T.ker ↔ ∃ g : E ≃ₗ[K] E, g.toLinearMap.comp S = T := by
  constructor
  · exact exists_postcomp_equiv_of_ker_eq S T
  · rintro ⟨g, rfl⟩
    ext x
    simp

end
end DFVSGames.Inverse.KMSKernelOrbits

namespace DFVSGames.Inverse.KMSBasisInvariant
noncomputable section
open scoped BigOperators
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Fourier.MatrixFourier

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

def primalChange (g : E ≃ₗ[F2] E) : (E →ₗ[F2] F) ≃ (E →ₗ[F2] F) where
  toFun X := X.comp g.toLinearMap
  invFun X := X.comp g.symm.toLinearMap
  left_inv X := by ext x; simp
  right_inv X := by ext x; simp

def frequencyChange (g : E ≃ₗ[F2] E) : (F →ₗ[F2] E) ≃ (F →ₗ[F2] E) where
  toFun S := g.toLinearMap.comp S
  invFun S := g.symm.toLinearMap.comp S
  left_inv S := by ext x; simp
  right_inv S := by ext x; simp

def IsBasisInvariant (f : (E →ₗ[F2] F) → ℝ) : Prop :=
  ∀ (g : E ≃ₗ[F2] E) X, f (X.comp g.toLinearMap) = f X

theorem character_change (g : E ≃ₗ[F2] E) (S : F →ₗ[F2] E)
    (X : E →ₗ[F2] F) :
    linearTraceCharacter (g.toLinearMap.comp S) X =
      linearTraceCharacter S (X.comp g.toLinearMap) := by
  simp only [linearTraceCharacter_apply, linearTracePair, LinearMap.comp_assoc]

variable [Fintype (E →ₗ[F2] F)]

theorem coefficient_change (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) (g : E ≃ₗ[F2] E) (S : F →ₗ[F2] E) :
    linearCoeff f (g.toLinearMap.comp S) = linearCoeff f S := by
  unfold linearCoeff
  apply Fintype.expect_equiv (primalChange g)
  intro X
  change f X * (linearTraceCharacter (g.toLinearMap.comp S) X).re =
    f (X.comp g.toLinearMap) * (linearTraceCharacter S (X.comp g.toLinearMap)).re
  rw [character_change, hf g X]

def frequencyRank (S : F →ₗ[F2] E) : ℕ := Module.finrank F2 (LinearMap.range S)

omit [Fintype (E →ₗ[F2] F)] in
theorem frequencyRank_change (g : E ≃ₗ[F2] E) (S : F →ₗ[F2] E) :
    frequencyRank (g.toLinearMap.comp S) = frequencyRank S := by
  unfold frequencyRank
  rw [LinearMap.range_comp, g.finrank_map_eq]

variable [Fintype (F →ₗ[F2] E)]

def rankProjection (i : ℕ) (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) : ℝ :=
  ∑ S, if frequencyRank S = i then linearCoeff f S * (linearTraceCharacter S X).re else 0

theorem rankProjection_invariant (i : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) : IsBasisInvariant (rankProjection i f) := by
  intro g X
  unfold rankProjection
  apply Fintype.sum_equiv (frequencyChange g)
  intro S
  change (if frequencyRank S = i then
      linearCoeff f S * (linearTraceCharacter S (X.comp g.toLinearMap)).re else 0) =
    if frequencyRank (g.toLinearMap.comp S) = i then
      linearCoeff f (g.toLinearMap.comp S) *
        (linearTraceCharacter (g.toLinearMap.comp S) X).re else 0
  rw [frequencyRank_change, coefficient_change f hf, character_change]

end
end DFVSGames.Inverse.KMSBasisInvariant

end OAI
