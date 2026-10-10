import OAI.NumberTheory.DirichletL.Inversion.InitialDyadicAssemblySourceCaps
import OAI.NumberTheory.DirichletL.Inversion.InitialDyadicAssemblyWindows

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialDyadicAssembly
open InverseInitialProfile CenteredMomentSectorLocalization CenteredMomentDyadicCount
open Filter

def retainedWindows (a b:Fin 4→ℝ)(Z D m L:ℝ) : Finset (Windows a b) :=
  Finset.univ.filter (fun k=>radialCenter m (exponent Z (k 3).val)
    (exponent Z (k 1).val) D (exponent Z (k 0).val)≤L)

def tailWindows (a b:Fin 4→ℝ)(Z D m L:ℝ) : Finset (Windows a b) :=
  Finset.univ.filter (fun k=>L<radialCenter m (exponent Z (k 3).val)
    (exponent Z (k 1).val) D (exponent Z (k 0).val))

theorem window_sum_split (a b:Fin 4→ℝ)(Z D m L:ℝ)(f:Windows a b→ℂ) :
    (∑k,f k)=(∑k∈retainedWindows a b Z D m L,f k)+
      ∑k∈tailWindows a b Z D m L,f k := by
  simpa only [retainedWindows,tailWindows,not_le] using
    (Finset.sum_filter_add_sum_filter_not (Finset.univ:Finset (Windows a b))
      (fun k=>radialCenter m (exponent Z (k 3).val) (exponent Z (k 1).val) D
        (exponent Z (k 0).val)≤L) f).symm

theorem retained_exponents_eventually (b R Λ:ℝ)(hb:0<b)(hR:0≤R)(hΛ:0≤Λ) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀D m L T:ℝ,D≤R→0≤m→L≤Λ→0<T→
      ∀k∈retainedWindows (fun _=>1) (physicalCaps b Z D T) Z D m L,
        ∀i,exponent Z (k i).val∈Set.Icc 0 (3*R+Λ+1) := by
  filter_upwards [window_exponent_eventual_upper b 1 hb (by norm_num)] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro D m L T hD hm hL hT k hk
  have hs:radialCenter m (exponent Z (k 3).val) (exponent Z (k 1).val) D
      (exponent Z (k 0).val)≤L := (Finset.mem_filter.mp hk).2
  have hp:0<b*Z^D := mul_pos hb (Real.rpow_pos_of_pos (by linarith [hZ.1]) D)
  have h0:=hZ.2 (b*Z^D) D hp le_rfl (k 0).val (k 0).property
  have h1:=hZ.2 (b*Z^D) D hp le_rfl (k 1).val (k 1).property
  have h2:=hZ.2 (b*Z^D) D hp le_rfl (k 2).val (k 2).property
  have h3:=window_exponent_nonneg Z T hZ.1 hT (k 3).val (k 3).property
  unfold radialCenter at hs
  intro i
  fin_cases i
  · change exponent Z (k 0).val∈Set.Icc 0 (3*R+Λ+1)
    exact ⟨h0.1,by linarith [h0.2]⟩
  · change exponent Z (k 1).val∈Set.Icc 0 (3*R+Λ+1)
    exact ⟨h1.1,by linarith [h1.2]⟩
  · change exponent Z (k 2).val∈Set.Icc 0 (3*R+Λ+1)
    exact ⟨h2.1,by linarith [h2.2]⟩
  · change exponent Z (k 3).val∈Set.Icc 0 (3*R+Λ+1)
    exact ⟨h3,by linarith [h0.1,h1.2]⟩

theorem window_quotient_eventually (b R:ℝ)(hb:0<b) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀D T η:ℝ,D≤R→0<T→η≤1→
      ∀k:Windows (fun _=>1) (physicalCaps b Z D T),
        exponent Z (k 0).val-exponent Z (k 1).val+2*η≤R+3 := by
  filter_upwards [window_exponent_eventual_upper b 1 hb (by norm_num)] with Z hz
  refine ⟨hz.1,?_⟩
  intro D T η hD hT hη k
  have hp:0<b*Z^D := mul_pos hb (Real.rpow_pos_of_pos (by linarith [hz.1]) D)
  have h0:=hz.2 (b*Z^D) D hp le_rfl (k 0).val (k 0).property
  have h1:=hz.2 (b*Z^D) D hp le_rfl (k 1).val (k 1).property
  linarith [h0.2,h1.1]

theorem retained_card_of_exponents (a b:Fin 4→ℝ)(Z D m L A:ℝ)(hZ:1<Z)
    (he:∀k∈retainedWindows a b Z D m L,∀i,exponent Z (k i).val∈Set.Icc 0 A) :
    (retainedWindows a b Z D m L).card≤
      Fintype.card (Windows (fun _=>1) (fun _=>Z^A)) := by
  have hZp:0<Z := by linarith
  let f:↥(retainedWindows a b Z D m L)→Windows (fun _=>1) (fun _=>Z^A) :=
    fun k i=>⟨(k.val i).val,(mem_indices_iff_scale 1 (Z^A) (by norm_num)
      (Real.rpow_pos_of_pos hZp A) (k.val i).val).mpr ⟨by
        rw [←exponent_scale Z hZ]
        simpa only [Real.rpow_zero] using
          (Real.rpow_le_rpow_left_iff hZ).mpr (he k.val k.property i).1,by
        have hh:(dyadicScale (k.val i).val)≤Z^A := by
          rw [←exponent_scale Z hZ]
          exact (Real.rpow_le_rpow_left_iff hZ).mpr (he k.val k.property i).2
        exact hh.trans (by nlinarith [Real.rpow_pos_of_pos hZp A])⟩⟩
  have hf:Function.Injective f := by
    intro k l h
    apply Subtype.ext
    funext i
    apply Subtype.ext
    simpa only [f] using congrArg Subtype.val (congrFun h i)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

theorem retained_card_subpower (b R Λ ε:ℝ)(hb:0<b)(hR:0≤R)(hΛ:0≤Λ)(hε:0<ε) :
    ∃A:ℝ,0<A ∧ ∀ᶠZ:ℝ in atTop,
      ∀D m L T:ℝ,D≤R→0≤m→L≤Λ→0<T→
        ((retainedWindows (fun _=>1) (physicalCaps b Z D T) Z D m L).card:ℝ)≤A*Z^ε := by
  obtain ⟨A,hA,hcount⟩:=windows_card_subpower 1 (3*R+Λ+1) ε (by norm_num) (by positivity) hε
  refine ⟨A,hA,?_⟩
  filter_upwards [retained_exponents_eventually b R Λ hb hR hΛ,hcount] with Z hz hc
  intro D m L T hD hm hL hT
  have he:=hz.2 D m L T hD hm hL hT
  have hi:=retained_card_of_exponents (fun _=>1) (physicalCaps b Z D T) Z D m L
    (3*R+Λ+1) hz.1 he
  have hp:(1:ℝ)≤Z^(3*R+Λ+1) := Real.one_le_rpow (le_of_lt hz.1) (by positivity)
  exact (by exact_mod_cast hi :
    ((retainedWindows (fun _=>1) (physicalCaps b Z D T) Z D m L).card:ℝ)≤
      (Fintype.card (Windows (fun _=>1) (fun _=>Z^(3*R+Λ+1))):ℝ)).trans
    (hc (fun _=>1) (fun _=>Z^(3*R+Λ+1)) (by intro i; norm_num)
      (fun _=>hp) (by intro i; simp))

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI
