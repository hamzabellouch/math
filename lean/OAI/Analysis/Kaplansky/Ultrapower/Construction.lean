import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Ultrapower.QuasiValue

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open scoped ComplexOrder ENNReal
open Filter Topology
open Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

lemma ultra_tendsto {ι : Type*} (u : Ultrafilter ι) (f : ι → ℝ) (C : ℝ)
    (h : ∀ i, |f i|≤C) : Tendsto f u (𝓝 (limUnder u f)) := by
  have hm : ((u.map f : Ultrafilter ℝ) : Filter ℝ) ≤ 𝓟 (Set.Icc (-C) C) := by
    apply le_principal_iff.mpr
    change ∀ᶠ i in (u : Filter ι), f i ∈ Set.Icc (-C) C
    exact Filter.Eventually.of_forall (fun i => abs_le.mp (h i))
  obtain ⟨x,_,hx⟩ := isCompact_Icc.ultrafilter_le_nhds (u.map f) hm
  exact tendsto_nhds_limUnder ⟨x,hx⟩

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
variable (V : QuasiValue A) {ι : Type*} (u : Ultrafilter ι)
abbrev Sequences := BoundedProduct (fun _ : ι => A)

omit [Nontrivial A] in
lemma seq_eval_selfAdjoint {a : Sequences (A:=A) (ι:=ι)} (ha : IsSelfAdjoint a) (i : ι) :
    IsSelfAdjoint (a i) := congrArg (fun x : Sequences (A:=A) (ι:=ι) => x i) ha.star_eq

omit [Nontrivial A] in
lemma seq_eval_commute {a b : Sequences (A:=A) (ι:=ι)} (h : Commute a b) (i : ι) :
    Commute (a i) (b i) := congrArg (fun x : Sequences (A:=A) (ι:=ι) => x i) h.eq

omit [Nontrivial A] in
lemma ultra_val_tendsto (a : Sequences (A:=A) (ι:=ι)) :
    Tendsto (fun i => V.val (a i)) u (𝓝 (limUnder u (fun i => V.val (a i)))) :=
  ultra_tendsto u _ ‖a‖ (fun i => (V.bound _).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero a i))

def ultra : QuasiValue (Sequences (A:=A) (ι:=ι)) where
  val a := limUnder u (fun i => V.val (a i))
  zero := by
    apply tendsto_nhds_unique (V.ultra_val_tendsto u 0)
    change Tendsto (fun _ : ι => V.val 0) u (𝓝 0)
    rw [V.zero]; exact tendsto_const_nhds
  one := by
    apply tendsto_nhds_unique (V.ultra_val_tendsto u 1)
    change Tendsto (fun _ : ι => V.val 1) u (𝓝 1)
    rw [V.one]; exact tendsto_const_nhds
  nonneg := by
    intro a ha
    exact ge_of_tendsto (V.ultra_val_tendsto u a) (Filter.Eventually.of_forall fun i =>
      V.nonneg ((boundedProduct_nonneg_iff a).mp ha i))
  mono := by
    intro a b ha hab
    exact le_of_tendsto_of_tendsto (V.ultra_val_tendsto u a) (V.ultra_val_tendsto u b)
      (Filter.Eventually.of_forall fun i => V.mono ((boundedProduct_nonneg_iff a).mp ha i)
        ((boundedProduct_le_iff a b).mp hab i))
  smul := by
    intro r a
    apply tendsto_nhds_unique (V.ultra_val_tendsto u (r • a))
    change Tendsto (fun i => V.val (r • a i)) u _
    simpa only [V.smul] using (V.ultra_val_tendsto u a).const_mul r
  bound := by
    intro a
    apply le_of_tendsto (V.ultra_val_tendsto u a).abs
    exact Filter.Eventually.of_forall fun i => (V.bound _).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero a i)
  lipschitz_positive := by
    intro a b ha hb
    apply le_of_tendsto ((V.ultra_val_tendsto u a).sub (V.ultra_val_tendsto u b)).abs
    exact Filter.Eventually.of_forall fun i =>
      (V.lipschitz_positive ((boundedProduct_nonneg_iff a).mp ha i)
        ((boundedProduct_nonneg_iff b).mp hb i)).trans
        (lp.norm_apply_le_norm ENNReal.top_ne_zero (a-b) i)
  square_swap := by
    intro a
    apply tendsto_nhds_unique (V.ultra_val_tendsto u (a*star a))
    change Tendsto (fun i => V.val (a i*star (a i))) u _
    have h := V.ultra_val_tendsto u (star a*a)
    change Tendsto (fun i => V.val (star (a i)*a i)) u _ at h
    simpa only [V.square_swap] using h
  weighted_add := by
    intro a b ha hb r hr
    apply le_of_tendsto_of_tendsto (V.ultra_val_tendsto u (a+b))
      (((V.ultra_val_tendsto u a).const_mul (1+r^2)).add
        ((V.ultra_val_tendsto u b).const_mul (1+r⁻¹^2)))
    exact Filter.Eventually.of_forall fun i => V.weighted_add
      ((boundedProduct_nonneg_iff a).mp ha i) ((boundedProduct_nonneg_iff b).mp hb i) r hr
  add_commute := by
    intro a b ha hb hc
    apply tendsto_nhds_unique (V.ultra_val_tendsto u (a+b))
    convert (V.ultra_val_tendsto u a).add (V.ultra_val_tendsto u b) using 1
    funext i
    exact V.add_commute (seq_eval_selfAdjoint ha i) (seq_eval_selfAdjoint hb i) (seq_eval_commute hc i)

def constHom : A →⋆ₐ[ℂ] Sequences (A:=A) (ι:=ι) where
  toFun a := ⟨fun _ => a,memℓp_infty ⟨‖a‖,by rintro _ ⟨i,rfl⟩; exact le_rfl⟩⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl
  commutes' _ := rfl

@[simp] lemma constHom_apply (a : A) (i : ι) : constHom (A:=A) (ι:=ι) a i=a := rfl

@[simp] lemma ultra_const (a : A) : (V.ultra u).val (constHom (A:=A) (ι:=ι) a)=V.val a := by
  exact tendsto_nhds_unique (V.ultra_val_tendsto u (constHom (A:=A) (ι:=ι) a)) tendsto_const_nhds


end KaplanskyConsequences.QuasiValue

end

end OAI
