import OAI.Combinatorics.HadwigerCounterexample.FiniteProjectionCenters

namespace OAI

/-! # Conditional Flags -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real
open scoped BigOperators
variable {A B C X Y : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype X] [Fintype Y]
variable {w : Wgt X}

def stained (w : Wgt X) (f : X→Y) (i : Y) : Wgt X := by
  classical exact if mapW w f i≠0 then onW w (fun x => f x=i) else w
theorem stained_law (f : X→Y) (hw : IsLaw w) (i : Y) : IsLaw (stained w f i) := by
  unfold stained; split
  next h => exact on_law hw.nz (lt_of_le_of_ne ((mapW_law hw f).nz _) (Ne.symm h))
  next => exact hw

theorem stain_rebuild (f : X→Y) (P : Y→Prop) (hw : IsLaw w) :
    subW w (P∘f) = mixW (subW (mapW w f) P) (stained w f) := by
  classical
  have hh := disintegrate hw.nz f
  funext i
  have hi (y) :
      mapW w f y * stained w f y i=
        mapW w f y * onW w (fun x => f x=y) i := by
    by_cases h : mapW w f y=0 <;> simp [stained,h]
  have he := congr_fun hh i
  unfold subW mixW Function.comp
  unfold mixW at he
  rw [he,avg,Finset.sum_mul]
  unfold avg at *
  apply sum_congr rfl
  intro j _
  rw [mul_right_comm _ (ind _), hi]
  by_cases hx : f i=j
  · rw [hx]
  simp only [onW_val,ind_zero hx,mul_zero,zero_div,zero_mul]

theorem stain_inputs (f : X→Y) (hw : IsLaw w) :
    w=mixW (mapW w f) (stained w f) := by
  have ht := stain_rebuild f (fun _ => True) hw
  unfold subW at ht
  simpa only [Function.comp_apply,ind_true,mul_one] using ht

variable {μ : Wgt A}

def colored (μ : Wgt A) (w : Wgt X) (v : A→ X→ Y) :=
  semi μ (fun i => mapW w (v i))
def coloredP (w : Wgt X) (v : A→ X→Y) (K : A→X→B) :=
  fun i : A×Y => mapW (stained w (v i.1) i.2) (K i.1)
def flaggedW (μ : Wgt A) (w : Wgt X) (v : A→X→Y) (K : A→X→B) (P : A→Y→Prop) :=
  mixW μ (fun i => mapW (subW w (P i ∘ v i)) (K i))

theorem semi_total (μ : Wgt A) (v : A → Wgt Y) :
    tot (semi μ v)=avg μ (fun i=>tot (v i)) := by
  simpa only [avg_const,mul_one] using semi_avg μ v (fun i=>1)

theorem colored_ultra (hμ : IsLaw μ) (hw : IsLaw w) (K : A→X→B) (v : A→X→Y) :
    Ultra (colored μ w v) (coloredP w v K) := by
  have ht (i) := mapW_law hw (v i)
  refine ⟨⟨fun x => mul_nonneg (hμ.nz _) ((ht _).nz _),?_⟩,
    fun i => mapW_law (stained_law _ hw _) (K i.1)⟩
  unfold colored; rw [semi_total]
  simp_rw [(ht _).total]
  exact hμ.avg_const _

theorem flag_catalog (K : A→ X→B) (v : A→ X→ Y) (P : A→ Y→ Prop)
    (hw : IsLaw w) (hμ : IsLaw μ) :
    catalog (colored μ w v) (coloredP w v K)
      (flaggedW μ w v K P) := by
  classical
  let W := colored μ w v
  have hh := (colored_ultra hμ hw K v).law
  refine ⟨subW W (fun i => P i.1 i.2),subW_nonneg hh.nz _,subW_le hh.nz _,?_⟩
  unfold flaggedW
  simp_rw [stain_rebuild (v _) (P _) hw,map_mix]
  funext x
  simp only [mixW,coloredP,colored,W,avg,subW,semi,Finset.mul_sum,Fintype.sum_prod_type]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

theorem colored_budget [Nonempty Y] (K : A→ X→B) (v : A→ X→ Y) (f : B→C)
    (hw : IsLaw w) (hμ : IsLaw μ) :
    budget (colored μ w v) (coloredP w v K) f ≤
      budget μ (fun i => mapW w (K i)) f + Real.log (num Y) := by
  unfold budget colored coloredP
  rw [semi_avg,← hμ.avg_const (Real.log _),← avg_add]
  apply avg_mono hμ.nz
  intro i
  let u := mapW w (v i)
  have he : IsLaw u := mapW_law hw (v i)
  let q (j : Y) := mapW (mapW (stained w (v i) j) (K i)) f
  have hq (j) : IsLaw (q j) := mapW_law (mapW_law (stained_law _ hw _) _) _
  have ht : mapW (mapW w (K i)) f=mixW u q := by
    calc mapW _ _ = mapW (mapW (mixW u (stained w (v i))) (K i)) f :=
                        congrArg (fun z => mapW (mapW z (K i)) f) (stain_inputs (v i) hw)
         _ = _ := by rw [map_mix,map_mix]
  change avg u (fun j => tension (q j) _)≤ tension _ _+_
  rw [tension_mix,add_comm _ (log _),ht]
  exact add_le_add_left (mix_charge he hq) _
end HadwigerCounterexample

end

end OAI
