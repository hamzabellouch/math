import Mathlib
import OAI.Geometry.CubicTorus.Profiles.CornerGrid155

namespace OAI

section
noncomputable section
namespace CubicTorus

lemma corner_grid_269 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
    (hd : (0/1 : ℝ)≤d) (he : d≤(13/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (3/4 : ℝ) with hm|hm
  · exact corner_grid_203 h hl hm hd he
  · exact corner_grid_268 h hm.le hu hd he

private lemma corner_grid_270 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (1/2 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (_hd : (13/45 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_271 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(168608/99225 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_272 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(17/32 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(15611552/10418625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_273 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/32 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(3546488/2480625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_274 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (17/32 : ℝ) with hm|hm
  · exact corner_grid_272 h hl hm hd he
  · exact corner_grid_273 h hm.le hu hd he

private lemma corner_grid_275 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (143/360 : ℝ) with hm|hm
  · exact corner_grid_271 h hl hu hd hm
  · exact corner_grid_274 h hl hu hm.le he

private lemma corner_grid_276 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(19/32 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(560384/375921 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_277 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/32 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(2420/1701 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_278 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (19/32 : ℝ) with hm|hm
  · exact corner_grid_276 h hl hm hd he
  · exact corner_grid_277 h hm.le hu hd he

private lemma corner_grid_279 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(19/32 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(12760352/9398025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_280 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/32 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(299/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(54494/42525 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_281 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/32 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (299/720 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(102553/85050 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_282 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/32 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (299/720 : ℝ) with hm|hm
  · exact corner_grid_280 h hl hu hd hm
  · exact corner_grid_281 h hl hu hm.le he

private lemma corner_grid_283 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (19/32 : ℝ) with hm|hm
  · exact corner_grid_279 h hl hm hd he
  · exact corner_grid_282 h hm.le hu hd he

private lemma corner_grid_284 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (143/360 : ℝ) with hm|hm
  · exact corner_grid_278 h hl hu hd hm
  · exact corner_grid_283 h hl hu hm.le he

private lemma corner_grid_285 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (9/16 : ℝ) with hm|hm
  · exact corner_grid_275 h hl hm hd he
  · exact corner_grid_284 h hm.le hu hd he

private lemma corner_grid_286 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/36 : ℝ) with hm|hm
  · exact corner_grid_270 h hl hu hd hm
  · exact corner_grid_285 h hl hu hm.le he

private lemma corner_grid_287 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(3324992/1913625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_288 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(21/32 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(13792/9275 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_289 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/32 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(11176/7875 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_290 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (21/32 : ℝ) with hm|hm
  · exact corner_grid_288 h hl hm hd he
  · exact corner_grid_289 h hm.le hu hd he

private lemma corner_grid_291 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/40 : ℝ) with hm|hm
  · exact corner_grid_287 h hl hu hd hm
  · exact corner_grid_290 h hl hu hm.le he

private lemma corner_grid_292 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(23/32 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(949888/637875 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_293 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/32 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(20141/14175 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_294 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (23/32 : ℝ) with hm|hm
  · exact corner_grid_292 h hl hm hd he
  · exact corner_grid_293 h hm.le hu hd he

private lemma corner_grid_295 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(23/32 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(10592/7875 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_296 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/32 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(247/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(3091/2450 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_297 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/32 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (247/720 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(133243/113400 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_298 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/32 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (247/720 : ℝ) with hm|hm
  · exact corner_grid_296 h hl hu hd hm
  · exact corner_grid_297 h hl hu hm.le he

private lemma corner_grid_299 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (23/32 : ℝ) with hm|hm
  · exact corner_grid_295 h hl hm hd he
  · exact corner_grid_298 h hm.le hu hd he

private lemma corner_grid_300 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/40 : ℝ) with hm|hm
  · exact corner_grid_294 h hl hu hd hm
  · exact corner_grid_299 h hl hu hm.le he

private lemma corner_grid_301 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (11/16 : ℝ) with hm|hm
  · exact corner_grid_291 h hl hm hd he
  · exact corner_grid_300 h hm.le hu hd he

private lemma corner_grid_302 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(21/32 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(40576/30051 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_303 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/32 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(91/240 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(13904/10935 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_304 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/32 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (91/240 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(253418/212625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_305 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/32 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/240 : ℝ) with hm|hm
  · exact corner_grid_303 h hl hu hd hm
  · exact corner_grid_304 h hl hu hm.le he

private lemma corner_grid_306 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (21/32 : ℝ) with hm|hm
  · exact corner_grid_302 h hl hm hd he
  · exact corner_grid_305 h hm.le hu hd he

private lemma corner_grid_307 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(21/32 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(299/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(900832/751275 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_308 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(21/32 : ℝ))
    (hd : (299/720 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(839992/751275 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_309 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(21/32 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (299/720 : ℝ) with hm|hm
  · exact corner_grid_307 h hl hu hd hm
  · exact corner_grid_308 h hl hu hm.le he

private lemma corner_grid_310 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/32 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(299/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(302984/273375 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_311 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/32 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (299/720 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1953578/1913625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_312 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/32 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (299/720 : ℝ) with hm|hm
  · exact corner_grid_310 h hl hu hd hm
  · exact corner_grid_311 h hl hu hm.le he

private lemma corner_grid_313 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (21/32 : ℝ) with hm|hm
  · exact corner_grid_309 h hl hm hd he
  · exact corner_grid_312 h hm.le hu hd he

private lemma corner_grid_314 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (143/360 : ℝ) with hm|hm
  · exact corner_grid_306 h hl hu hd hm
  · exact corner_grid_313 h hl hu hm.le he

private lemma corner_grid_315 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(23/32 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(91/240 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(30208/25515 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_316 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(23/32 : ℝ))
    (hd : (91/240 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(77752/70875 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_317 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(23/32 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/240 : ℝ) with hm|hm
  · exact corner_grid_315 h hl hu hd hm
  · exact corner_grid_316 h hl hu hm.le he

private lemma corner_grid_318 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/32 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(91/240 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(4301/3969 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_319 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/32 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (91/240 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(87109/88200 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_320 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/32 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/240 : ℝ) with hm|hm
  · exact corner_grid_318 h hl hu hd hm
  · exact corner_grid_319 h hl hu hm.le he

private lemma corner_grid_321 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (23/32 : ℝ) with hm|hm
  · exact corner_grid_317 h hl hm hd he
  · exact corner_grid_320 h hm.le hu hd he

private lemma corner_grid_322 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(23/32 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(299/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(641632/637875 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_323 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(23/32 : ℝ))
    (hd : (299/720 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(580792/637875 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_324 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(23/32 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (299/720 : ℝ) with hm|hm
  · exact corner_grid_322 h hl hu hd hm
  · exact corner_grid_323 h hl hu hm.le he

private lemma corner_grid_325 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/32 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(299/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(176011/198450 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_326 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/32 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (299/720 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(12661/16200 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_327 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/32 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (299/720 : ℝ) with hm|hm
  · exact corner_grid_325 h hl hu hd hm
  · exact corner_grid_326 h hl hu hm.le he

private lemma corner_grid_328 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (23/32 : ℝ) with hm|hm
  · exact corner_grid_324 h hl hm hd he
  · exact corner_grid_327 h hm.le hu hd he

private lemma corner_grid_329 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (143/360 : ℝ) with hm|hm
  · exact corner_grid_321 h hl hu hd hm
  · exact corner_grid_328 h hl hu hm.le he

private lemma corner_grid_330 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (11/16 : ℝ) with hm|hm
  · exact corner_grid_314 h hl hm hd he
  · exact corner_grid_329 h hm.le hu hd he

private lemma corner_grid_331 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/36 : ℝ) with hm|hm
  · exact corner_grid_301 h hl hu hd hm
  · exact corner_grid_330 h hl hu hm.le he

lemma corner_grid_332 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (5/8 : ℝ) with hm|hm
  · exact corner_grid_286 h hl hm hd he
  · exact corner_grid_331 h hm.le hu hd he

private lemma corner_grid_333 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(17/32 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1582592/1157625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_334 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/32 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(65/144 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(50864/39375 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_335 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/32 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (65/144 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(3454/2835 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_336 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/32 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (65/144 : ℝ) with hm|hm
  · exact corner_grid_334 h hl hu hd hm
  · exact corner_grid_335 h hl hu hm.le he

private lemma corner_grid_337 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (17/32 : ℝ) with hm|hm
  · exact corner_grid_333 h hl hm hd he
  · exact corner_grid_336 h hm.le hu hd he

private lemma corner_grid_338 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(17/32 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(39/80 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1822304/1488375 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_339 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(17/32 : ℝ))
    (hd : (39/80 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(147752/128625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_340 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(17/32 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (39/80 : ℝ) with hm|hm
  · exact corner_grid_338 h hl hu hd hm
  · exact corner_grid_339 h hl hu hm.le he

private lemma corner_grid_341 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/32 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(39/80 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(2832632/2480625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_342 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/32 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (39/80 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(32538/30625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_343 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/32 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (39/80 : ℝ) with hm|hm
  · exact corner_grid_341 h hl hu hd hm
  · exact corner_grid_342 h hl hu hm.le he

private lemma corner_grid_344 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (17/32 : ℝ) with hm|hm
  · exact corner_grid_340 h hl hm hd he
  · exact corner_grid_343 h hm.le hu hd he

private lemma corner_grid_345 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (169/360 : ℝ) with hm|hm
  · exact corner_grid_337 h hl hu hd hm
  · exact corner_grid_344 h hl hu hm.le he

private lemma corner_grid_346 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(19/32 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(65/144 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1265792/1044225 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_347 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(19/32 : ℝ))
    (hd : (65/144 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(426536/375921 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_348 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(19/32 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (65/144 : ℝ) with hm|hm
  · exact corner_grid_346 h hl hu hd hm
  · exact corner_grid_347 h hl hu hm.le he

private lemma corner_grid_349 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/32 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(65/144 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(5324/4725 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_350 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/32 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (65/144 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(3553/3402 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_351 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/32 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (65/144 : ℝ) with hm|hm
  · exact corner_grid_349 h hl hu hd hm
  · exact corner_grid_350 h hl hu hm.le he

private lemma corner_grid_352 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (19/32 : ℝ) with hm|hm
  · exact corner_grid_348 h hl hm hd he
  · exact corner_grid_351 h hm.le hu hd he

private lemma corner_grid_353 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(19/32 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(39/80 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(9904928/9398025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_354 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(19/32 : ℝ))
    (hd : (39/80 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(112552/116025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_355 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(19/32 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (39/80 : ℝ) with hm|hm
  · exact corner_grid_353 h hl hu hd hm
  · exact corner_grid_354 h hl hu hm.le he

private lemma corner_grid_356 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/32 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(39/80 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(40766/42525 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_357 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/32 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (39/80 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(913/1050 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_358 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/32 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (39/80 : ℝ) with hm|hm
  · exact corner_grid_356 h hl hu hd hm
  · exact corner_grid_357 h hl hu hm.le he

private lemma corner_grid_359 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (19/32 : ℝ) with hm|hm
  · exact corner_grid_355 h hl hm hd he
  · exact corner_grid_358 h hm.le hu hd he

private lemma corner_grid_360 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (169/360 : ℝ) with hm|hm
  · exact corner_grid_352 h hl hu hd hm
  · exact corner_grid_359 h hl hu hm.le he

lemma corner_grid_361 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (9/16 : ℝ) with hm|hm
  · exact corner_grid_345 h hl hm hd he
  · exact corner_grid_360 h hm.le hu hd he

private lemma corner_grid_362 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(17/32 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(377/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(11149952/10418625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_363 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(17/32 : ℝ))
    (hd : (377/720 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(10302248/10418625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_364 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(17/32 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (377/720 : ℝ) with hm|hm
  · exact corner_grid_362 h hl hu hd hm
  · exact corner_grid_363 h hl hu hm.le he

private lemma corner_grid_365 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/32 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(377/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(2431088/2480625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_366 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/32 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (377/720 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(2219162/2480625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_367 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/32 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (377/720 : ℝ) with hm|hm
  · exact corner_grid_365 h hl hu hd hm
  · exact corner_grid_366 h hl hu hm.le he

private lemma corner_grid_368 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (17/32 : ℝ) with hm|hm
  · exact corner_grid_364 h hl hm hd he
  · exact corner_grid_367 h hm.le hu hd he

private lemma corner_grid_369 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(17/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(5984/6615 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_370 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(17/32 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(8517608/10418625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_371 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(17/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (403/720 : ℝ) with hm|hm
  · exact corner_grid_369 h hl hu hd hm
  · exact corner_grid_370 h hl hu hm.le he

private lemma corner_grid_372 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/32 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(8888/11025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_373 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/32 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(253286/354375 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_374 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/32 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (403/720 : ℝ) with hm|hm
  · exact corner_grid_372 h hl hu hd hm
  · exact corner_grid_373 h hl hu hm.le he

private lemma corner_grid_375 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (17/32 : ℝ) with hm|hm
  · exact corner_grid_371 h hl hm hd he
  · exact corner_grid_374 h hm.le hu hd he

lemma corner_grid_376 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/24 : ℝ) with hm|hm
  · exact corner_grid_368 h hl hu hd hm
  · exact corner_grid_375 h hl hu hm.le he

private lemma corner_grid_377 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(19/32 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(377/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1185536/1342575 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_378 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(19/32 : ℝ))
    (hd : (377/720 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7451048/9398025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

lemma corner_grid_379 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(19/32 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (377/720 : ℝ) with hm|hm
  · exact corner_grid_377 h hl hu hd hm
  · exact corner_grid_378 h hl hu hm.le he

lemma corner_grid_380 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/32 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(377/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(33044/42525 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

end CubicTorus
end
end

end OAI
