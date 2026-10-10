import OAI.MeasureTheory.Falconer.Estimates.ScalarScaleAlignment

namespace OAI

/-! Translation and positive zooming preserve scalar cell counts up to
 the single carry in a translated grid. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_translation_cells (δ b : ℝ) (X : Finset ℝ) :
    (scalarCells δ (X.image (fun x => x+b))).card ≤ 2*(scalarCells δ X).card := by
  have he : X.image (fun x => x+b) = X+{b} := by
    ext z
    simp only [Finset.mem_image,Finset.mem_add,Finset.mem_singleton]
    aesop
  rw [he]
  have hh := scalarCells_add_card δ X {b}
  have hc : (scalarCells δ X+scalarCells δ {b}).card ≤ (scalarCells δ X).card := by
    simpa only [scalarCells,Finset.image_singleton,Finset.card_singleton,mul_one] using
      (Finset.card_add_le (s := scalarCells δ X) (t := scalarCells δ {b}))
  exact hh.trans (Nat.mul_le_mul_left 2 hc)

 theorem scalar_zoom_cells {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) (z : ℝ) (X : Finset ℝ) :
    (scalarCells (δ/R) (scalarZoom z R X)).card ≤ 2*(scalarCells δ X).card := by
  have he : scalarCells (δ/R) (scalarZoom z R X) =
      scalarCells δ (X.image (fun x => x+(-z))) := by
    unfold scalarCells scalarZoom
    rw [Finset.image_image,Finset.image_image]
    apply Finset.image_congr
    intro x _
    change ⌊((x-z)/R)/(δ/R)⌋ = ⌊(x+(-z))/δ⌋
    congr 1
    field_simp
    ring
  rw [he]
  exact scalar_translation_cells δ (-z) X

 theorem scalar_zoom_linear_sum (z R a : ℝ) (X : Finset ℝ) :
    scalarZoom z R X+(scalarZoom z R X).image (fun x => a*x) =
      scalarZoom ((1+a)*z) R (X+X.image (fun x => a*x)) := by
  ext t
  constructor
  · intro ht
    obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_add.mp ht
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hw
    refine Finset.mem_image.mpr ⟨x+a*y,Finset.add_mem_add hx (Finset.mem_image.mpr ⟨y,hy,rfl⟩),?_⟩
    ring
  · intro ht
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨x,hx,v,hv,rfl⟩ := Finset.mem_add.mp hu
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
    refine Finset.mem_add.mpr ⟨(x-z)/R,Finset.mem_image.mpr ⟨x,hx,rfl⟩,
      a*((y-z)/R),Finset.mem_image.mpr ⟨(y-z)/R,Finset.mem_image.mpr ⟨y,hy,rfl⟩,rfl⟩,?_⟩
    ring

end Falconer

end OAI
