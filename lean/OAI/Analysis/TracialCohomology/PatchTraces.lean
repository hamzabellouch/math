import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.LocalQuantization

namespace OAI

/-! Patch traces for bounded Hochschild cohomology. -/

noncomputable section

open scoped ComplexOrder
namespace PopaPatching
open BoundedHochschild HochschildRigidity
variable {G M : Type*} [Group G] [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

namespace Rep

def inCorner (v : Rep G M) {p : M} (hp : IsStarProjection p) (hv : v.support=p) :
    G →* PopaCorner.algebra hp where
  toFun g := ⟨v g,by
    change p*v g=v g ∧ v g*p=v g
    rw [←hv]
    exact ⟨v.support_mul g,v.mul_support g⟩⟩
  map_one' := Subtype.ext hv
  map_mul' g h := Subtype.ext (v.mul g h)

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma inCorner_coe (v : Rep G M) {p : M} (hp : IsStarProjection p) (hv) (g) :
    ((inCorner v hp hv g : PopaCorner.algebra hp):M)=v g := rfl

omit [PartialOrder M] [StarOrderedRing M] in
lemma inCorner_norm_le (v : Rep G M) {p : M} (hp : IsStarProjection p) (hv) (g) :
    ‖inCorner v hp hv g‖≤1 := v.norm_le g
end Rep

variable {K : Type*}
omit [PartialOrder M] [StarOrderedRing M] in
lemma prod_norm_le (l : List K) (A : K → M) (hA : ∀ i ∈ l, ‖A i‖≤1) :
    ‖(l.map A).prod‖≤1 := by
  induction l with
  | nil => exact (IsStarProjection.one M).norm_le
  | cons i l ih =>
    exact (norm_mul_le _ _).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (hA i (by simp))).trans
        (ih (fun j hj => hA j (by simp [hj]))))

lemma prod_gns_sub_le (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (l : List K) (A B : K → M) (hA : ∀ i ∈ l, ‖A i‖≤1) (hB : ∀ i ∈ l, ‖B i‖≤1) :
    ‖τ.toPreGNS ((l.map A).prod-(l.map B).prod)‖≤
      (l.map (fun i => ‖τ.toPreGNS (A i-B i)‖)).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hA' := fun j hj => hA j (List.mem_cons_of_mem i hj)
    have hB' := fun j hj => hB j (List.mem_cons_of_mem i hj)
    have hh := ih hA' hB'
    have he : A i*(l.map A).prod-B i*(l.map B).prod=
        A i*((l.map A).prod-(l.map B).prod)+(A i-B i)*(l.map B).prod := by noncomm_ring
    simp only [List.map_cons,List.prod_cons,List.sum_cons]
    rw [he,map_add]
    calc
      _ ≤ ‖τ.toPreGNS (A i*((l.map A).prod-(l.map B).prod))‖+
          ‖τ.toPreGNS ((A i-B i)*(l.map B).prod)‖ := norm_add_le _ _
      _ ≤ ‖τ.toPreGNS ((l.map A).prod-(l.map B).prod)‖+
          ‖τ.toPreGNS (A i-B i)‖ := by
        apply add_le_add
        · exact (preGNS_norm_mul_le τ _ _).trans
            (mul_le_of_le_one_left (norm_nonneg _) (hA i (by simp)))
        · exact (preGNS_norm_mul_right_le τ htr _ _).trans
            (mul_le_of_le_one_left (norm_nonneg _) (prod_norm_le l B hB'))
      _ ≤ _ := by linarith

lemma prod_gns_sub_uniform (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (l : List K) (A B : K → M) (hA : ∀ i ∈ l, ‖A i‖≤1) (hB : ∀ i ∈ l, ‖B i‖≤1)
    (θ : ℝ) (he : ∀ i ∈ l, ‖τ.toPreGNS (A i-B i)‖≤θ) :
    ‖τ.toPreGNS ((l.map A).prod-(l.map B).prod)‖≤(l.length:ℝ)*θ := by
  refine (prod_gns_sub_le τ htr l A B hA hB).trans ?_
  calc
    _ ≤ (l.map (fun _ => θ)).sum := List.sum_le_sum (fun i hi => he i hi)
    _ = _ := by simp

lemma corner_scalar_norm_le (τ : M →ₚ[ℂ] ℂ) (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) (Y : M) (hY : ‖Y‖≤1) :
    ‖PopaCorner.trace hp τ (PopaCorner.compress hp Y)‖≤1 := by
  exact (HochschildUltrapower.norm_trace_le (PopaCorner.trace hp τ)
    (PopaCorner.trace_one hp τ hfaith hp0) _).trans
    ((preGNS_norm_le (PopaCorner.trace hp τ) (PopaCorner.trace_one hp τ hfaith hp0) _).trans
      ((PopaCorner.compress_norm_le hp Y).trans hY))

lemma trace_rescale (τ : M →ₚ[ℂ] ℂ) (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) (a : PopaCorner.algebra hp) :
    τ (a:M)=((τ p).re:ℂ)*PopaCorner.trace hp τ a := by
  have ht : (τ p).re ≠ 0 := (HochschildDiffuse.projection_trace_pos τ hfaith hp hp0).ne'
  rw [PopaCorner.trace_apply,←mul_assoc,←Complex.ofReal_mul,mul_inv_cancel₀ ht,Complex.ofReal_one,one_mul]

omit [StarOrderedRing M] in
lemma trace_product_compress (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (w : Rep G M) {q : M} (hq : IsStarProjection q) (hw : w.support=q)
    (l : List K) (g : K → G) (Y : K → M) (hl : l ≠ []) :
    τ ((l.map (fun j => w (g j)*Y j)).prod) =
      τ (((l.map (fun j => w.inCorner hq hw (g j)*PopaCorner.compress hq (Y j))).prod :
        PopaCorner.algebra hq):M) := by
  have hleft (ls : List K) : q*((ls.map (fun j => w (g j)*Y j)).prod*q)=
      (ls.map (fun j => w (g j)*Y j)).prod*q := by
    cases ls with
    | nil => simpa using hq.isIdempotentElem.eq
    | cons j ls =>
      simp only [List.map_cons,List.prod_cons,←mul_assoc]
      rw [←hw,w.support_mul]
  have he (ls : List K) :
      (((ls.map (fun j => w.inCorner hq hw (g j)*PopaCorner.compress hq (Y j))).prod :
        PopaCorner.algebra hq):M) = (ls.map (fun j => w (g j)*Y j)).prod*q := by
    induction ls with
    | nil => simp
    | cons j ls ih =>
      change (w (g j)*(q*Y j*q))*
        (((ls.map (fun j => w.inCorner hq hw (g j)*PopaCorner.compress hq (Y j))).prod :
          PopaCorner.algebra hq):M) = (w (g j)*Y j)*(ls.map (fun j => w (g j)*Y j)).prod*q
      rw [ih]
      have hwq : w (g j)*q=w (g j) := by rw [←hw,w.mul_support]
      rw [←mul_assoc (w (g j)),←mul_assoc (w (g j)),hwq]
      rw [mul_assoc (w (g j)*Y j),hleft]
      simp only [mul_assoc]
  rw [he,htr _ q]
  cases l with
  | nil => exact False.elim (hl rfl)
  | cons j ls =>
    simp only [List.map_cons,List.prod_cons,←mul_assoc]
    rw [←hw,w.support_mul]

omit [PartialOrder M] [StarOrderedRing M] in
lemma scalar_product (w : Rep G M) {q : M} (hq : IsStarProjection q) (hw : w.support=q)
    (l : List K) (g : K → G) (c : K → ℂ) :
    (l.map (fun j => w.inCorner hq hw (g j)*(c j • 1))).prod=
      (l.map c).prod • w.inCorner hq hw ((l.map g).prod) := by
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [List.map_cons,List.prod_cons]
    rw [ih,map_mul]
    simp only [mul_smul_comm,mul_one,smul_mul_assoc,smul_smul,mul_comm]

theorem block_trace_error (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (w : Rep G M) {q : M} (hq : IsStarProjection q) (hq0 : q ≠ 0) (hw : w.support=q)
    (l : List K) (g : K → G) (Y : K → M) (c : K → ℂ) (hl : l ≠ [])
    (hY : ∀ j ∈ l, ‖Y j‖≤1) (hc : ∀ j ∈ l, ‖c j‖≤1)
    (θ : ℝ) (he : ∀ j ∈ l,
      ‖(PopaCorner.trace hq τ).toPreGNS (PopaCorner.compress hq (Y j)-c j • 1)‖≤θ) :
    ‖τ ((l.map (fun j => w (g j)*Y j)).prod)-
      (l.map c).prod*τ (w ((l.map g).prod))‖≤(l.length:ℝ)*θ*(τ q).re := by
  let t := PopaCorner.trace hq τ
  let A := fun j => w.inCorner hq hw (g j)*PopaCorner.compress hq (Y j)
  let B := fun j => w.inCorner hq hw (g j)*(c j • 1)
  have ht1 : t 1=1 := PopaCorner.trace_one hq τ hfaith hq0
  have hA (j) (hj : j ∈ l) : ‖A j‖≤1 := (norm_mul_le _ _).trans
    ((mul_le_of_le_one_left (norm_nonneg _) (w.inCorner_norm_le hq hw _)).trans
      ((PopaCorner.compress_norm_le hq _).trans (hY j hj)))
  have hB (j) (hj : j ∈ l) : ‖B j‖≤1 := by
    apply (norm_mul_le _ _).trans
    apply (mul_le_of_le_one_left (norm_nonneg _) (w.inCorner_norm_le hq hw _)).trans
    rw [norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hc j hj)).trans (IsStarProjection.one _).norm_le
  have hE (j) (hj : j ∈ l) : ‖t.toPreGNS (A j-B j)‖≤θ := by
    change ‖t.toPreGNS (w.inCorner hq hw (g j)*PopaCorner.compress hq (Y j)-
      w.inCorner hq hw (g j)*(c j • 1))‖≤θ
    rw [←mul_sub]
    exact (preGNS_norm_mul_le t _ _).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (w.inCorner_norm_le hq hw _)).trans (he j hj))
  have hnorm := (HochschildUltrapower.norm_trace_le t ht1 _).trans
    (prod_gns_sub_uniform t (PopaCorner.trace_tracial hq τ htr) l A B hA hB θ hE)
  have ht : 0<(τ q).re := HochschildDiffuse.projection_trace_pos τ hfaith hq hq0
  have hscalar := scalar_product w hq hw l g c
  have hvtrace : τ (w ((l.map g).prod))=
      ((τ q).re:ℂ)*t (w.inCorner hq hw ((l.map g).prod)) :=
    trace_rescale τ hfaith hq hq0 (w.inCorner hq hw ((l.map g).prod))
  rw [trace_product_compress τ htr w hq hw l g Y hl,trace_rescale τ hfaith hq hq0,hvtrace]
  have heq : ((τ q).re:ℂ)*t ((l.map A).prod)-
      (l.map c).prod*(((τ q).re:ℂ)*t (w.inCorner hq hw ((l.map g).prod))) =
      ((τ q).re:ℂ)*t ((l.map A).prod-(l.map B).prod) := by
    rw [map_sub]
    change _ = _*(t ((l.map A).prod)-t ((l.map (fun j => w.inCorner hq hw (g j)*(c j • 1))).prod))
    rw [hscalar,map_smul,smul_eq_mul]
    ring
  change ‖((τ q).re:ℂ)*t ((l.map A).prod)-(l.map c).prod*
    (((τ q).re:ℂ)*t (w.inCorner hq hw ((l.map g).prod)))‖≤_
  rw [heq,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht]
  nlinarith
end PopaPatching

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaCorner PopaPatching
variable {G M K : Type*} [Group G] [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
lemma cyclic_product_compress {N : Type*} (T : M → N) (hT : ∀ a b : M, T (a*b)=T (b*a))
    (w : Rep G M) {q : M} (hq : IsStarProjection q) (hw : w.support=q)
    (l : List K) (g : K → G) (Y : K → M) (hl : l ≠ []) :
    T ((l.map (fun j => w (g j)*Y j)).prod) =
      T (((l.map (fun j => w.inCorner hq hw (g j)*PopaCorner.compress hq (Y j))).prod :
        PopaCorner.algebra hq):M) := by
  have hleft (ls : List K) : q*((ls.map (fun j => w (g j)*Y j)).prod*q)=
      (ls.map (fun j => w (g j)*Y j)).prod*q := by
    cases ls with
    | nil => simpa using hq.isIdempotentElem.eq
    | cons j ls =>
      simp only [List.map_cons,List.prod_cons,←mul_assoc]
      rw [←hw,w.support_mul]
  have he (ls : List K) :
      (((ls.map (fun j => w.inCorner hq hw (g j)*PopaCorner.compress hq (Y j))).prod :
        PopaCorner.algebra hq):M) = (ls.map (fun j => w (g j)*Y j)).prod*q := by
    induction ls with
    | nil => simp
    | cons j ls ih =>
      change (w (g j)*(q*Y j*q))*
        (((ls.map (fun j => w.inCorner hq hw (g j)*PopaCorner.compress hq (Y j))).prod :
          PopaCorner.algebra hq):M) = (w (g j)*Y j)*(ls.map (fun j => w (g j)*Y j)).prod*q
      rw [ih]
      have hwq : w (g j)*q=w (g j) := by rw [←hw,w.mul_support]
      rw [←mul_assoc (w (g j)),←mul_assoc (w (g j)),hwq]
      rw [mul_assoc (w (g j)*Y j),hleft]
      simp only [mul_assoc]
  rw [he,hT _ q]
  cases l with
  | nil => exact False.elim (hl rfl)
  | cons j ls =>
    simp only [List.map_cons,List.prod_cons,←mul_assoc]
    rw [←hw,w.support_mul]

omit [PartialOrder M] [StarOrderedRing M] in
lemma central_list_prod (l : List K) (c : K → M) (hc : ∀ j, Central (c j)) :
    Central ((l.map c).prod) := by
  induction l with
  | nil => exact fun x => Commute.one_left _
  | cons j l ih => exact central_mul (hc j) ih

omit [PartialOrder M] [StarOrderedRing M] in
lemma compress_central {q : M} (hq : IsStarProjection q) {c : M} (hc : Central c) :
    ((compress hq c):M)=c*q := by
  change q*c*q=c*q
  rw [←(hc q).eq,mul_assoc,hq.isIdempotentElem.eq]

omit [PartialOrder M] [StarOrderedRing M] in
lemma central_product (w : Rep G M) {q : M} (hq : IsStarProjection q) (hw : w.support=q)
    (l : List K) (g : K → G) (c : K → M) (hc : ∀ j, Central (c j)) :
    (((l.map (fun j => w.inCorner hq hw (g j)*compress hq (c j))).prod : algebra hq):M)=
      (l.map c).prod*w ((l.map g).prod) := by
  induction l with
  | nil => simp [←hw,Rep.support]
  | cons j l ih =>
    change (w (g j)*((compress hq (c j)):M))*
      (((l.map (fun j => w.inCorner hq hw (g j)*compress hq (c j))).prod : algebra hq):M)=_
    have hterm : w (g j)*((compress hq (c j)):M)=c j*w (g j) := by
      rw [compress_central hq (hc j),←mul_assoc,←(hc j (w (g j))).eq,
        mul_assoc (c j) (w (g j)),←hw,w.mul_support]
    rw [hterm,ih]
    simp only [List.map_cons,List.prod_cons,w.mul]
    calc
      _ = c j*(w (g j)*(l.map c).prod)*w ((l.map g).prod) := by simp only [mul_assoc]
      _ = _ := by rw [←(central_list_prod l c hc (w (g j))).eq]; simp only [mul_assoc]

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include h1 in
theorem block_average_error (w : Rep G M) {q : M} (hq : IsStarProjection q) (hq0 : q ≠ 0)
    (hw : w.support=q) (hEq : average e τ hτ htr hfaith q=(τ q).re • (1:M))
    (l : List K) (g : K → G) (Y c : K → M) (hcZ : ∀ j, Central (c j)) (hl : l ≠ [])
    (hY : ∀ j ∈ l, ‖Y j‖≤1) (hc : ∀ j ∈ l, ‖c j‖≤1)
    (θ : ℝ) (hθ : 0≤θ) (he : ∀ j ∈ l,
      ‖(trace hq τ).toPreGNS (compress hq (Y j)-compress hq (c j))‖≤θ) :
    ‖τ.toPreGNS (average e τ hτ htr hfaith ((l.map (fun j => w (g j)*Y j)).prod)-
      (l.map c).prod*average e τ hτ htr hfaith (w ((l.map g).prod)))‖≤(l.length:ℝ)*θ*(τ q).re := by
  let t := trace hq τ
  let A := fun j => w.inCorner hq hw (g j)*compress hq (Y j)
  let B := fun j => w.inCorner hq hw (g j)*compress hq (c j)
  have hA (j) (hj : j ∈ l) : ‖A j‖≤1 := (norm_mul_le _ _).trans
    ((mul_le_of_le_one_left (norm_nonneg _) (w.inCorner_norm_le hq hw _)).trans
      ((compress_norm_le hq _).trans (hY j hj)))
  have hB (j) (hj : j ∈ l) : ‖B j‖≤1 := (norm_mul_le _ _).trans
    ((mul_le_of_le_one_left (norm_nonneg _) (w.inCorner_norm_le hq hw _)).trans
      ((compress_norm_le hq _).trans (hc j hj)))
  have hE (j) (hj : j ∈ l) : ‖t.toPreGNS (A j-B j)‖≤θ := by
    change ‖t.toPreGNS (w.inCorner hq hw (g j)*compress hq (Y j)-
      w.inCorner hq hw (g j)*compress hq (c j))‖≤θ
    rw [←mul_sub]
    exact (preGNS_norm_mul_le t _ _).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (w.inCorner_norm_le hq hw _)).trans (he j hj))
  have hh := average_corner_error e τ hτ htr hfaith h1 hq hq0 hEq
    ((l.map A).prod-(l.map B).prod) (mul_nonneg (Nat.cast_nonneg _) hθ)
    (prod_gns_sub_uniform t (trace_tracial hq τ htr) l A B hA hB θ hE)
  rw [cyclic_product_compress (average e τ hτ htr hfaith) (average_trace e τ hτ htr hfaith h1) w hq hw l g Y hl]
  have heq : average e τ hτ htr hfaith (((l.map A).prod-(l.map B).prod : algebra hq):M)=
      average e τ hτ htr hfaith (((l.map A).prod : algebra hq):M)-
      (l.map c).prod*average e τ hτ htr hfaith (w ((l.map g).prod)) := by
    change expectation e τ hτ htr hfaith h1 (_-_)=_
    rw [map_sub]
    change _-average e τ hτ htr hfaith (((l.map (fun j => w.inCorner hq hw (g j)*compress hq (c j))).prod : algebra hq):M)=_
    rw [central_product w hq hw l g c hcZ,average_bimodule e τ hτ htr hfaith h1 (central_list_prod l c hcZ)]
    rfl
  rw [heq] at hh
  exact hh.trans_eq (by ring)
end PopaCenter

end

end OAI
